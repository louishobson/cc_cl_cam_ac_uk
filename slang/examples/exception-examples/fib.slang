let fib (m : int) : int = 
    try
        if m = 0
        then 0 
        else if m = 1 
            then 1 
            else raise fib (m - 1) + fib (m - 2) 
            end 
        end 
    with (x : int) -> 
        x
    end
in 
    fib(?) 
end