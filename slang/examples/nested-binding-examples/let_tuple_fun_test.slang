let rev ((x : int, y : int), (z : bool, w : int)) : int * int = if z then (y, x) else (x, y) end
     in 
        snd ( rev ((21, 17), (true, 1)) ) 
     end 