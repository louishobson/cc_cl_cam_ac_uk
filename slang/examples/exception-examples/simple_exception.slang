try
    raise try 
        if true then raise 1 else 0 end
    with ( x : int ) -> 
        x + 11
    end
with ( x : int ) ->
    x + 100
end