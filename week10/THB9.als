abstract sig Entry {
    parent: lone Dir
}
sig File extends Entry {}
sig Dir extends Entry {}
one sig Root extends Dir {}

fact Cautructhumuc {

    no Root.parent // Nút gốc thì không có cha

    all e: Entry - Root | one e.parent // Mỗi phần tử khác gốc có đúng một thư mục cha

    all d: Dir | d !in d.parent // Một thư mục không được là cha của chính nó

    all d1, d2: Dir | d1 in d2.parent implies d2 !in d1.parent // Hai thư mục không được đồng thời là cha của nhau

    all d: Dir | d !in d.^parent // Bổ sung fact
}

assert MoiTepDeuCoCha {
    all f: File | some f.parent
}

assert KhongChuTrinhBaTMKhac {
    no disj d1, d2, d3: Dir | d1 in d2.parent and d2 in d3.parent and d3 in d1.parent
}

assert MoiThuMuc {
    all d: Dir - Root | d.parent = Root
}

check MoiTepDeuCoCha for 5
check KhongChuTrinhBaTMKhac for 5
check MoiThuMuc for 5