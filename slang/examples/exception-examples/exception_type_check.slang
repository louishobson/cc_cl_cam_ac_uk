try
    try 
        if true then raise 0 else 1 end
    with ( x : int ) -> 
        raise x + 11
    end
with ( x : bool ) ->
    if x then 100 else 101 end
end