import copy
from collections import defaultdict
import random
import networkx as nx
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import set_ev_cls, CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.lib.packet import ethernet, ether_types, arp, ipv6
from ryu.ofproto import ofproto_v1_3
from ryu.topology import event
from ryu.topology.api import get_switch, get_link
from ryu.lib.packet import packet
import matplotlib.pyplot as plt
import os.path


class Topo(object):
    # 当创建一个类时进行数据初始化
    def __init__(self):
        # self.switches 存放所有的交换机的dpid
        self.switches = []
        # self.adjdict 存放所有交换机之间的端口连接 但是这里要注意keyerrors
        self.adjdict = {}
        self.adjlist = []
        # 并查集
        self.father = []
        self.rank = []
        # 记录最小生成树路径上每个结点附近的结点
        self.path = {}

    # 初始化adjdict的get和set方法
    def set_adjdict(self, s1, s2, port):
        if s1 not in self.adjdict.keys():
            self.adjdict[s1] = {}
        self.adjdict[s1][s2] = port

    def get_adjdict(self, s1):
        return self.adjdict[s1]

    # 并查集的寻找父亲结点函数
    def find_father(self, sw):
        return sw if sw == self.father[sw] else self.find_father(self.father[sw])

    # 并查集的归并函数 按按秩合并 将简单的簇并入复杂的簇
    def union(self, new_sw, pre_sw):
        new = self.father[new_sw]
        pre = self.find_father(pre_sw)
        # 简单的并入复杂的，防止高度变长太多
        if self.rank[new] <= self.rank[pre]:
            self.father[new] = pre
        else:
            self.father[pre] = new
        if self.rank[new] == self.rank[pre] and new != pre:
            self.rank[pre] += 1

    # # 返回最小生成树的边集合
    # 初始化（按秩合并）
    # inline void init(int n)
    # {
    # for (int i = 1; i <= n; ++i)
    # {
    #     fa[i] = i;
    # rank[i] = 1;
    # }
    # }

    # 得到所有边和权重的边集
    def get_list(self):
        # 用于判断该交换机是否被遍历过
        isFlag = [False] * (len(self.switches) + 1)
        # 遍历所有交换机的边 给所有交换机之间的边随机赋一个权值加入边集adjlist中
        for sw1 in self.adjdict.keys():
            for sw2 in self.adjdict[sw1].keys():
                if isFlag[sw2] is False:
                    w = random.randint(1, 5)
                    self.adjlist.append((sw1, sw2, w))
                    self.adjlist.append((sw2, sw1, w))
            isFlag[sw1] = True

    # 使用Kruskal算法 返回的是最小生成树的边
    def kruskal(self):
        # 初始化father和rank
        # print(self.switches)
        self.father = [None] * (len(self.switches) + 1)
        self.rank = [1] * (len(self.switches) + 1)
        # print(self.adjdict.keys())
        for sw in self.adjdict.keys():
            # print(self.father)
            self.father[sw] = sw
        # 判断所有交换机是否连通 如果不连通直接返回
        if len(self.switches) <= 0 or len(self.adjlist) < len(self.switches) - 1:
            return
        # 按权重排序 得到权重从小到大的边列表 self.adjlist -> (sw1,sw2,weight) 所以x[2]为权重
        self.adjlist.sort(key=lambda x: x[2])
        # print(self.adjlist)
        # tree_links用于存储画图用的最小生成树边
        tree_links = []
        # all_links用于存储交换机之间所有的边
        all_links = [(adj[0], adj[1]) for adj in self.adjlist]
        # print(all_links)
        # weight用于存储所有交换机之间边的权重
        weights = dict(zip(all_links, [adj[2] for adj in self.adjlist]))
        # print(weights)
        # kruskal算法的核心部分 从权重最小的边开始选择 保证每个结点只加入一次 直到所有结点都被选择
        for List in self.adjlist:
            # 用并查集判断两个结点是否在同一个簇里面
            if self.find_father(List[0]) != self.find_father(List[1]):
                # 将两个结点合并为同一个簇
                self.union(List[0], List[1])
                # 初始化队列防止出现error
                if List[0] not in self.path.keys():
                    self.path[List[0]] = []
                if List[1] not in self.path.keys():
                    self.path[List[1]] = []
                # self.path存储最小生成树的边
                self.path[List[0]].append(List[1])
                self.path[List[1]].append(List[0])
                tree_links.append((List[0], List[1]))
                tree_links.append((List[1], List[0]))
        # 画出最小生成树
        draw_graph(all_links, tree_links, weights)
        # print("---------------------",self.path)

    # 实现找到一个交换机邻接的交换机 并调用kruskal
    # def find_borsw(self, sw):
    #     # 给边集赋值
    #     if len(self.adjlist) is 0:
    #         self.get_list()
    #     if len(self.path) is 0:
    #         self.kruskal()
    #     if sw not in self.path.keys():
    #         print("广播交换机输入错误,请重新开始程序")
    #         return
    #
    #     return self.path[sw]

    # def choice_borsw(self, sw):
    #     bor_sw = self.find_borsw(sw)
    #     print("请选择灌包的主机（显示的是选定的广播主机最小生成树上邻接的主机）:（", end=' ')
    #     for x in bor_sw:
    #         print(x, end=' ')
    #     print('）')
    #     choice = int(input())
    #     # print(bor_sw,'  ',type(bor_sw[0]))
    #     if choice not in bor_sw:
    #         print("灌包输入错误,请重新开始程序")
    #         return None
    #     return choice

    # 返回两个相邻交换机的路径
    # def find_bor_path(self, src_sw, dst_sw):
    #     return [(src_sw, 1, [self.get_adjdict(src_sw)[dst_sw]]), (dst_sw, self.get_adjdict(dst_sw)[src_sw], [1])]

    # 实现选定任意交换机根据最小生成树的路径得到这个交换机广播到其他交换机的配置路径
    # 我们想要得到 (switch,inport,outport) 用于配置路径 我们现有边隔壁的所有点
    def compute_flowTables(self, src_sw, first_port):
        # 调用函数得到最小生成树的边集
        self.get_list()
        self.kruskal()
        # result 用于存储要配置的路径 格式 -> (switch,inport,outport)
        result = []
        # 设计一个栈用遍历算法遍历出从源节点出发的所有的路径
        stack = [src_sw]
        # 记录每个交换机对应的inport
        inports = [None] * (len(self.switches) + 1)
        inports[src_sw] = first_port
        # 记录每个交换机对应的outport
        outports = []
        # 记录是否结点已经被遍历过 都初始化为false
        isFlag = [False] * (len(self.switches) + 1)
        while len(stack) != 0:
            cur = stack.pop()
            isFlag[cur] = True
            # 把该结点的相邻结点加进去 同时加入到配置路径里面
            # print(self.path[cur])
            for sw in self.path[cur]:
                if isFlag[sw] is False:
                    # 注意交换机的inport和上一个交换机连接过来的outport并不一样 嗯 在这里出错过
                    inports[sw] = self.get_adjdict(sw)[cur]
                    outports.append(self.get_adjdict(cur)[sw])
                    stack.append(sw)
            result.append((cur, inports[cur], outports))
            # 除了广播交换器，其他每个交换机都要配置一个1的outport实现广播
            outports = [1]
        # print("配置的路径：",result)
        return result

    # bfs找到两个交换机之间的最短路
    def find_bor_path(self, src_sw, dst_sw):
        # the front lines are the same as dfs
        # sign records a switch whether is visited
        sign = {}
        # 用于存放最短配置路径
        result = []
        # init sign as 0,a switch one sign
        for sw in self.switches:
            sign[sw] = 0
        sign[src_sw] = -1
        # use list function as queue
        queue_list = [src_sw]
        # bfs find the shortest way
        while queue_list:
            sw = queue_list.pop()
            if sw == dst_sw:
                print("最短路径已经找出来了:", end=" ")
                self.printsPath(sw, sign, result, 1)
                print("end")
                return result
            for u in self.get_adjdict(sw).keys():
                if sign[u] == 0:
                    sign[u] = sw
                    queue_list.insert(0, u)
    # 用于输出最短路路径 与project1相同
    def printsPath(self, sw, sign, result, outport):  # [(4, 3, [1]), (3, 1, [3])]
        if sign[sw] != -1:
            result.append((sw, self.get_adjdict(sw)[sign[sw]], [outport]))
            self.printsPath(sign[sw], sign, result, self.get_adjdict(sign[sw])[sw])
        elif sign[sw] == -1:
            result.append((sw, 1, [outport]))
        print(f"{sw}-", end=' ')


class Controller(app_manager.RyuApp):
    # openflow version 1.3
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(Controller, self).__init__(*args, **kwargs)
        self.sw_to_mac = {'1': '00:00:00:00:00:01',
                          '2': '00:00:00:00:00:02',
                          '3': '00:00:00:00:00:03',
                          '4': '00:00:00:00:00:04',
                          '5': '00:00:00:00:00:05',
                          '6': '00:00:00:00:00:06',
                          '7': '00:00:00:00:00:07',
                          '8': '00:00:00:00:00:08',
                          '9': '00:00:00:00:00:09',
                          '10': '00:00:00:00:00:10',
                          '11': '00:00:00:00:00:11',
                          '12': '00:00:00:00:00:12',
                          '13': '00:00:00:00:00:ff'}
        self.topo = Topo()
        self.datapaths = []
        self.arp_history = {}
        self.arp_table = {'192.168.0.1': '00:00:00:00:00:01',
                          '192.168.0.2': '00:00:00:00:00:02',
                          '192.168.0.3': '00:00:00:00:00:03',
                          '192.168.0.4': '00:00:00:00:00:04',
                          '192.168.0.5': '00:00:00:00:00:05',
                          '192.168.0.6': '00:00:00:00:00:06',
                          '192.168.0.7': '00:00:00:00:00:07',
                          '192.168.0.8': '00:00:00:00:00:08',
                          '192.168.0.9': '00:00:00:00:00:09',
                          '192.168.0.10': '00:00:00:00:00:10',
                          '192.168.0.11': '00:00:00:00:00:11',
                          '192.168.0.12': '00:00:00:00:00:12',
                          '192.168.0.255': '00:00:00:00:00:ff'
                          }
        # 初始化时选定要广播和灌包的交换机
        self.bro_sw = int(input("请输入要对外广播的交换机（1-13）:"))
        assert 0 < self.bro_sw < 14
        self.bor_sw = int(input("请输入要灌包的交换机（1-13）:"))
        assert 0 < self.bor_sw  < 14 and self.bor_sw != self.bro_sw
        # 判断广播路径是否已经设定
        self.flag = False

    # 参考simple_switch_13改编
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        # 一开始 Switch 連上 Controller 时的初始设定Function
        datapath = ev.msg.datapath  # 接收 OpenFlow 交换器
        ofproto = datapath.ofproto  # OpenFlow 交换器使用的 OF 协定版本
        parser = datapath.ofproto_parser  # 处理 OF 协定的 parser（解析器）

        # install table-miss flow entry
        #
        # We specify NO BUFFER to max_len of the output action due to
        # OVS bug. At this moment, if we specify a lesser number, e.g.,
        # 128, OVS will send Packet-In with invalid buffer_id and
        # truncated packet data. In that case, we cannot output packets
        # correctly.  The bug has been fixed in OVS v2.1.0.
        # 以下片段yon'gu Table-Miss FlowEntry
        # 首先新增一个空的 match，也就是能够 match 任何封包的 match rule
        match = parser.OFPMatch()
        # 指定这一条 Table-Miss FlowEntry 的对应行为
        # 把所有不知道如何处理的封包都送到 Controller
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        # 把 Table-Miss FlowEntry 設定至 Switch，並指定优先权為 0 (最低)
        self.add_flow(datapath, 0, match, actions)

    def add_flow(self, datapath, priority, match, actions, buffer_id=None):
        # 取得与 Switch 使用的 IF 版本 对应的 OF 协定及 parser
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        # Instruction 是定义当封包满足 match 時，所要执行的动作
        # 因此把 action 以 OFPInstructionActions 包裝起來
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        # FlowMod Function 可以讓我們對 Switch 寫入由我們所定義的 Flow Entry
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
            # 把定义好的 FlowEntry 送給 Switch
        datapath.send_msg(mod)

    # 参考simple_switch_13改编
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        # 收到來自 Switch 不知如何處理的封包（Match 到 Table-Miss FlowEntry）
        # If you hit this you might want to increase
        # the "miss_send_length" of your switch
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes",
                              ev.msg.msg_len, ev.msg.total_len)
        # 获取包的基本信息
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']
        pkt = packet.Packet(msg.data)
        # eth 里面 存储着包的源和目标mac地址
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        # 如果还没配置过广播路径 进行配置
        if not self.flag:
            # 所有最小生成树配置路径的集合
            path = self.topo.compute_flowTables(self.bro_sw, 1)
            print('最小生成树路径:  ', path)
            # 给路径中交换机下发流表
            # print(bro_sw,type(bro_sw))
            # print("mac:",self.sw_to_mac[str(bro_sw)])
            # print("mac:",self.sw_to_mac[str(bor_sw)])
            # 对路径进行配置
            self.configure_path(path, ev, self.sw_to_mac[str(self.bro_sw)], self.sw_to_mac[str(self.bor_sw)])
            print('***********************路径设置完成************************')
            # print(self.topo.find_bor_path(self.bor_sw, self.bro_sw))
            # 下发回路
            # 由于前面的配置只实现了对外广播的交换机到其他交换机的路径配置，而灌包时需要两个交换机能ping通 所以同时也要配置灌包交换机到广播交换机的路径
            # 这里路径是通过project1的BFS算法得到的
            self.configure_path(self.topo.find_bor_path(self.bor_sw, self.bro_sw), ev, self.sw_to_mac[str(self.bor_sw)],
                                self.sw_to_mac[str(self.bro_sw)])
            print('***********************路径设置完成************************')
            # 路径配置完成，将flag标志为true，防止重复配置出错
            self.flag = True
        # 丢弃泛洪的包
        if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
            return
        # 记录src和dst的mac地址
        dst = eth.dst
        src = eth.src
        dpid = datapath.id
        # arp包
        arp_pkt = pkt.get_protocol(arp.arp)
        if arp_pkt:
            # 记录到arp表中 ip->mac
            self.arp_table[arp_pkt.src_ip] = src

        # 丢弃ipv6的包 监听端口不同 不丢弃可能会造成大量丢包
        if pkt.get_protocol(ipv6.ipv6):
            # match = parser.OFPMatch(eth_type=eth.ethertype)
            # actions = []
            # self.add_flow(datapath, 1, match, actions)
            return None
        # print(dst)
        # 如果是广播帧 判断是否记录过arp表
        if dst == 'ff:ff:ff:ff:ff:ff':
            # print(self.arp_handler(msg))
            if self.arp_handler(msg):
                return

    # after add_flow switch enter we should put it in class we defined
    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, event):
        self.logger.info("A switch entered.")
        self.switch_topoFind_handler(event)
        self.logger.info("Find all topology switches we can find\n")

    @set_ev_cls(event.EventSwitchLeave)
    def switch_leave_handler(self, event):
        self.logger.info("A switch leaved.")
        self.switch_topoFind_handler(event)
        self.logger.info("Find all topology switches we can find\n")

    def switch_topoFind_handler(self, event):
        # 找到已连接的所有交换机 ps.这里的switches和topo里面定义的switches不一样
        switches = copy.copy(get_switch(self, None))
        # 把所有已连接交换机的dpid放在topo.switches内
        self.topo.switches = [sw.dp.id for sw in switches]
        self.logger.info("switches: {}".format(self.topo.switches))
        # 把所有已连接交换机的datapath放在datapaths中
        self.datapaths = [sw.dp for sw in switches]

        # 得到所有交换机之间的拓扑连接   a links is like（格式） : (src_sw,dst_sw,inport,outport)
        links = copy.copy(get_link(self, None))
        # 把所有拓扑连接的数据放在列表links_msg里面
        links_msg = [(l.src.dpid, l.dst.dpid, l.src.port_no, l.dst.port_no) for l in links]
        self.logger.info("All links({}):".format(len(links_msg)))
        for src, dst, ip, op in links_msg:
            # 拓扑是双向的
            self.topo.set_adjdict(src, dst, ip)
            self.topo.set_adjdict(dst, src, op)
            self.logger.info(f"link from sw:{src} port:{ip} to sw{dst} port:{op} ")

    def configure_path(self, path, event, src_mac, dst_mac):
        # configure shortest path to switches
        msg = event.msg
        datapath = msg.datapath

        ofproto = datapath.ofproto

        parser = datapath.ofproto_parser

        # 获取选择路径经过的交换机以及转发方式，配置match和actions
        # (s1,inport,outport)->(s2,inport,outport)->...->(dest_switch,inport,outport)
        for switch, inport, outportList in path:
            match = parser.OFPMatch(in_port=inport, eth_src=src_mac, eth_dst=dst_mac)

            actions = []
            # actions是一个列表，表示流表向哪些端口转发 与project1的不同之处在于配置路径时,传入的path中的outport是列表 需要配置多个输出端口
            for outport in outportList:
                actions.append(parser.OFPActionOutput(outport))

            # 找到dpid对应的datapath
            datapath = self._find_dp(int(switch))
            assert datapath is not None

            inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]

            # idle and hardtimeout set to 0,making the entry permanent
            # reference openflow spec
            mod = datapath.ofproto_parser.OFPFlowMod(
                datapath=datapath,
                match=match,
                idle_timeout=0,
                hard_timeout=0,
                priority=1,
                instructions=inst
            )
            # 下发流表
            datapath.send_msg(mod)

    def _find_dp(self, dpid):
        for dp in self.datapaths:
            if dp.id == dpid:
                return dp
        return None

    # refer https://www.cnblogs.com/caijigugujiao/p/14664276.html can see for more detail
    def arp_handler(self, msg):
        # 包的基本数据
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']
        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        arp_pkt = pkt.get_protocol(arp.arp)
        # void error
        dst_mac = ''
        src_mac = ''
        if eth:
            dst_mac = eth.dst
            src_mac = eth.src
        # """
        #     解决环路风暴：
        #         在回复ARP请求之前，必须解决的是网络环路问题。
        #             解决方案是：
        #                 以(dpid,eth_src,arp_dst_ip)为key，
        #                 记录第一个数据包的in_port，并将从网络中返回的数据包丢弃，
        #                 保证同一个交换机中的某一个广播数据包只能有一个入口，
        #                 从而防止成环。在此应用中，默认网络中发起通信的第一个数据包都是ARP数据包。
        #  """
        # 判断该包是不是广播包
        if dst_mac == 'ff:ff:ff:ff:ff:ff' and arp_pkt:
            # target ip
            dst_ip = arp_pkt.dst_ip
            src_ip = arp_pkt.src_ip
            # 判断这个包有没有经过过这个交换机
            if (datapath.id, src_ip, dst_ip) in self.arp_history:
                # 如果这个包已经从别的端口进入过这个交换机
                if self.arp_history[(datapath.id, src_ip, dst_ip)] != in_port:
                    return True
            else:
                # 这个包第一次到达这个交换机记录下来
                self.arp_history[(datapath.id, src_ip, dst_ip)] = in_port
                print(f"{datapath.id} first come ,arp learn this switch")
        # """
        #     ARP回复：
        #         解决完环路拓扑中存在的广播风暴问题之后，要利用SDN控制器获取网络全局的信息的能力，去代理回复ARP请求，
        #         从而减少网络中泛洪的ARP请求数据。通过自学习主机ARP记录，在通过查询记录并回复。
        # """
        if arp_pkt:
            opcode = arp_pkt.opcode
            if opcode == arp.ARP_REQUEST:
                # hardware type
                hwtype = arp_pkt.hwtype
                # protocol type
                proto = arp_pkt.proto
                # hardware address length
                hlen = arp_pkt.hlen
                # protocol address length
                plen = arp_pkt.plen
                # src ip
                arp_src_ip = arp_pkt.src_ip
                # dst ip
                arp_dst_ip = arp_pkt.dst_ip
                if arp_dst_ip in self.arp_table:
                    actions = [parser.OFPActionOutput(in_port)]
                    arp_reply = packet.Packet()
                    arp_reply.add_protocol(ethernet.ethernet(
                        ethertype=eth.ethertype,
                        dst=src_mac,
                        src=self.arp_table[arp_dst_ip]))
                    # add arp protocol
                    arp_reply.add_protocol(arp.arp(
                        opcode=arp.ARP_REPLY,
                        src_mac=self.arp_table[arp_dst_ip],
                        src_ip=arp_dst_ip,
                        dst_mac=src_mac,
                        dst_ip=arp_src_ip))
                    arp_reply.serialize()
                    # arp reply
                    out = parser.OFPPacketOut(
                        datapath=datapath,
                        buffer_id=ofproto.OFP_NO_BUFFER,
                        in_port=ofproto.OFPP_CONTROLLER,
                        actions=actions, data=arp_reply.data)
                    datapath.send_msg(out)

                    return True
        return False


# draw
def draw_graph(sw, link, weight):
    plt.figure()
    # extract nodes from graph
    nodes = set([n1 for n1, n2 in sw] + [n2 for n1, n2 in sw])
    # create networkx graph
    G = nx.Graph()
    # add nodes
    for node in nodes:
        G.add_node(node)
    # add edges
    G.add_edges_from(sw, color='b')
    G.add_edges_from(link, color='r')
    # draw graph
    pos = nx.spring_layout(G)
    # nodes
    nx.draw_networkx_nodes(G, pos, node_size=450)
    # edges
    nx.draw_networkx_edges(G, pos, edgelist=sw, edge_color='b')
    nx.draw_networkx_edges(G, pos, edgelist=link, edge_color='r')
    # labels
    nx.draw_networkx_labels(G, pos, font_size=8, font_family='sans-serif')
    nx.draw_networkx_edge_labels(G, pos, weight, font_size=8)
    plt.axis('off')

    # show graph
    # 尽量不要用中文
    plt.savefig("最小生成树.jpg")
