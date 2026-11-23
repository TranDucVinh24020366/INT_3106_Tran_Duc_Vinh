abstract sig Entry {
  parent: lone Dir
}
sig File extends Entry {}
sig Dir extends Entry {}
one sig Root extends Dir {}


fact {
  no Root.parent
  all e: Entry - Root | one e.parent
  no d: Dir | d in d.^parent // Với mọi thư mục d thì d không được nằm trong tập tổ tiên của chính nó.
  all e: Entry | Root in e.*parent // Với mọi phần tử e thuộc Entry, đi ngược quan hệ parent từ 0 bước trở lên đều phải tới Root.
  all d: Dir | #(parent.d) <= 3 // Với mọi thư mục d, số lượng phần tử nằm trực tiếp bên trong d nhiều nhất là 3 phần tử.
}


pred TepGocBaCanh {
  some f: File | Root in f.parent.parent.parent
}
run TepGocBaCanh for 6
run TepGocBaCanh for 8

pred ThuMucChuaHaiTep {
  some d: Dir | #(File & parent.d) = 2
}
run ThuMucChuaHaiTep for 6
run ThuMucChuaHaiTep for 8

pred ThuMucChuaBaTep{
  some d: Dir | #(File & (^parent).d) >= 3
}
run ThuMucChuaBaTep for 6
run ThuMucChuaBaTep for 8

assert MoiPhanTuKhacGocCoToTienLaGoc {
  all e: Entry - Root | Root in e.^parent
}
check MoiPhanTuKhacGocCoToTienLaGoc for 6
check MoiPhanTuKhacGocCoToTienLaGoc for 8

assert ToTienBatDoiXung {
  all a, b: Entry | a in b.^parent implies b !in a.^parent
}
check ToTienBatDoiXung for 6
check ToTienBatDoiXung for 8

assert CayConToiDaBaTep {
  all d: Dir | #(parent.d) <= 3 implies #(File & (^parent).d) <= 3
}
check CayConToiDaBaTep for 6
check CayConToiDaBaTep for 8