define i32 @foo(i32 %n) {
  %1 = add i32 %n, %n
  ret i32 %1
}

define i32 @main(i32 %argc, i8** %arcv) {
  %1 = call i32 @foo(i32 4)
  ret i32 %1
}
