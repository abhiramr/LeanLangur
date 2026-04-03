def smallest(items):
    match items:
        case [x]:
            return x
        case [x, y, *zs]:
            smallest_in_tail = smallest([y, *zs])
            return min(x, smallest_in_tail)

print(smallest([5, 3, 8, 1, 4])) # 1

print(smallest([])) # None