# Algorithm 10 in SQIsign documentation
# return a quaternion in O0 of norm M
function FullRepresentInteger(M::Integer)
    counter = 0
    found = false
    x, y, z, w = 0, 0, 0, 0
    while !found && counter < KLPT_repres_num_gamma_trial
        m = integer_square_root(div(4*M, p))
        z = rand(-m:m)
        md = integer_square_root(div(4*M - z^2, p))
        w = rand(-md:md)
        Md = 4*M - p*(z^2 + w^2)
        x, y, found = sum_of_two_squares(Md)
        if !found || (x - w) % 2 != 0 || (y - z) % 2 != 0
            found = false
            counter += 1
        end
    end
    if found
        return QOrderElem(div(x - w, 2), div(y - z, 2), z, w), found
    else
        return Quaternion_0, found
    end
end
