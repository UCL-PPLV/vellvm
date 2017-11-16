define i64 @factorial(i64 %n) {
; <label> 0
  %1 = alloca i64
  %acc = alloca i64
  ; void instr 0
  store i64 %n, i64* %1
  ; void instr 1
  store i64 1, i64* %acc
  br label %start
start:
  %2 = load i64, i64* %1
  %3 = icmp sgt i64 %2, 0
  br i1 %3, label %then, label %end
then:
  %4 = load i64, i64* %acc
  %5 = load i64, i64* %1
  %6 = mul i64 %4, %5
  ; void instr 4
  store i64 %6, i64* %acc
  %7 = load i64, i64* %1
  %8 = sub i64 %7, 1
  ; void instr 5
  store i64 %8, i64* %1
  br label %start
end:
  %9 = load i64, i64* %acc
  ret i64 %9
}
define i64 @main(i64 %argc, i8** %arcv) {
; <label> 0
  %1 = alloca i64
  ; void instr 0
  store i64 0, i64* %1
  %2 = call i64 @factorial(i64 5)
  ret i64 %2
}