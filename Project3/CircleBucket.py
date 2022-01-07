"""
定义一个循环桶的类
1. 建一个指定容量的桶，存放(w[u],u)类型数据并能根据w[u]的大小放入相应的位置。  w[u]为结点u离源点的位置
2. 能对桶内的数据进行更新修改，并重新放置。
3. 在取出一个数据后，能自动将桶的头指针位置转移到桶内w[u]最小的桶。
"""


class CircleBucket(object):
    def __init__(self, buckets_num):
        # 桶中存放数据的个数
        self.buckets_num = buckets_num
        # 创建桶数组 用于存放(w[u],[u])类型数据 因为距离源点同一距离的点不一定只有一个
        self.buckets = [[] for i in range(self.buckets_num)]
        # 桶的头指针位置 默认为0
        self.first_bucket = 0
        # 桶中所以数据个数
        self.data_num = 0

    # 更新桶的头指针位置
    def updateFirst(self):
        # 如果现在头指针位置的列表为空
        if self.checkListEmpty(self.first_bucket):
            self.first_bucket = (self.first_bucket + 1) % self.buckets_num
            while self.checkListEmpty(self.first_bucket):
                self.first_bucket = (self.first_bucket + 1) % self.buckets_num

    # 获得桶的头指针的数据
    def getFirst(self):
        # 先进行头指针的更新
        self.updateFirst()
        # 如果列表不为空才进行操作
        self.data_num -= 1
        return self.buckets[self.first_bucket].pop()

    # 向桶内更新数据 将w位置的桶内加入u 即源结点到u的距离为w
    def updateBucket(self, w, u):
        # 向桶内加入数据 每个桶里面都是一个列表
        self.buckets[w % self.buckets_num].append(u)
        self.data_num += 1

    def checkListEmpty(self, w):
        # 如果列表为空 返回true
        if not self.buckets[w]:
            return True
        return False

    # 判断桶内是否有数据
    def checkBucketEmpty(self):
        return self.data_num == 0
