try
    try 
        if true then raise ((ref 1), 1) else ((ref 2), 2) end
    with ( x : (int ref) * int ) -> 
        let (r : int ref, v : int ) = x 
        in
            if !r = 1 then ((raise true), 3) else ((ref 4), 4) end
        end
    end
with ( x : bool ) ->
    if x then ((ref 4), 4) else ((ref 5), 5) end
end