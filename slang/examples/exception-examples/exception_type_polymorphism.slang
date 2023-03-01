try
    try 
        if true then raise (ref 1) else (ref 2) end
    with ( x : int ref ) -> 
        if !x = 1 then (raise true) else (ref 3) end
    end
with ( x : bool ) ->
    if x then (ref 4) else (ref 5) end
end