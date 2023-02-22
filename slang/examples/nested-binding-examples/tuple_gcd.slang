
let gcd (m : int, n : int) : int = 
    if m = n 
    then m 
    else if m < n 
        then gcd(m, n - m)
        else gcd(m - n, n)
        end 
    end
in gcd(?, ?) end