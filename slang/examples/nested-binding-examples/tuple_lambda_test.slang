let f : ((int * int) * bool) -> (int * int) = 
   (fun ((x : int, y : int), z : bool) -> if z then (y, x) else (x, y) end end)
in
   f ((1, 2), true)
end
     