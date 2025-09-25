def fadd(val1, b1, val2, b2):
    return val1 + val2, b1 + b2

def main():
    x = (2, 5)
    y = (3, 7)
    z_val, z_bound = fadd(x[0], x[1], y[0], y[1])
    print(f"x={x}, y={y} -> z=({z_val}, {z_bound}) ; feasible={z_val <= z_bound}")

if __name__ == "__main__":
    main()
