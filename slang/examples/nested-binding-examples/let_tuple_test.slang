let rev (p : (int * int) * bool) : (int * int) = 
   let ((x : int, y : int), z : bool) = p in
      if z then (y, x) else (x, y) end
   end
   in 
      snd ( rev ((21, 17), true) ) 
   end 