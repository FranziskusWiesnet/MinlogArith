import math
import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
import random

def fit_poly_least_squares(xs, ys, deg, through_origin=True):
    """
    Least-squares polynomial fit using SymPy.

    Parameters
    ----------
    xs, ys : lists of numbers
        Data points (x_i, y_i) to be fitted.
    deg : int
        Maximum polynomial degree.
    through_origin : bool
        If True, enforce p(0)=0 by omitting the constant term.

    Returns
    -------
    poly_expr : SymPy expression
        The fitted polynomial as a SymPy expression.
    """
    x = sp.Symbol("x", real=True)

    powers = list(range(1, deg + 1)) if through_origin else list(range(0, deg + 1))

    # Build the design matrix A and the target vector b for least squares:
    # a_{i,j} = (x_i)^(powers[j]),  b_i = y_i
    a = sp.Matrix([[sp.Integer(x) ** p for p in powers] for x in xs])
    b = sp.Matrix([sp.Float(y) for y in ys])

    # Solve the least-squares problem A*c ≈ b
    c = a.solve_least_squares(b)

    # Assemble the polynomial from the coefficients c
    poly = sum(c[j] * x**powers[j] for j in range(len(powers)))
    return sp.expand(poly)

def sse(xs, ys, poly_expr):
    """
       Compute the sum of squared errors (SSE) for a polynomial model.
    """
    x = sp.Symbol("x", real=True)
    f = sp.lambdify(x, poly_expr, "math")
    return sum((float(yy) - float(f(xx)))**2 for xx, yy in zip(xs, ys))

def bic(xs, ys, poly_expr, num_params):
    """
    Bayesian Information Criterion (BIC) for model selection.

    Lower BIC is better. BIC trades off goodness-of-fit (via SSE) against
    model complexity (number of parameters).
    """
    n = len(xs)
    SSE = max(sse(xs, ys, poly_expr), 1e-300)
    return n * math.log(SSE / n) + num_params * math.log(n)

def select_degree_by_bic(xs, ys, max_deg=10, through_origin=True):
    """
    Fit polynomials of degree 1..max_deg and return the one with minimal BIC.
    """
    best = None
    for deg in range(1, max_deg + 1):
        poly = fit_poly_least_squares(xs, ys, deg, through_origin=through_origin)

        # Number of free parameters:
        # - with p(0)=0 constraint: deg coefficients (x^1..x^deg)
        # - otherwise: deg+1 coefficients (1...x^deg)
        num_params = deg if through_origin else (deg + 1)
        score = bic(xs, ys, poly, num_params)
        if best is None or score < best["bic"]:
            best = {"deg": deg, "poly": poly, "bic": score}
    return best

if __name__ == '__main__':

    # Measured runtimes (in seconds) for different algorithms / settings.
    ys_sqrt = [1.88, 8.69, 22.37, 43.12, 79.33, 115.76, 169.47, 225.10, 296.10, 375.22]
    dist_sqrt = "20,000"

    ys_fastsqrt = [0.08, 0.26, 0.67, 1.05, 2.02, 2.72, 3.69, 4.66, 6.65, 8.08]
    dist_fastsqrt = "5,000"

    ys_stein =     [0.34, 1.08, 2.33, 3.89, 5.64, 8.09, 10.71, 14.07, 17.56, 21.46]
    dist_stein = "10,000"

    ys_euclid =    [1.61, 6.55, 15.31, 29.09, 49.25, 72.34, 105.28, 141.89, 190.42, 242.94]
    dist_euclid = "500"

    ys_extStein =  [0.07, 0.29, 0.68, 1.43, 2.52, 3.85, 5.85, 8.11, 11.39, 14.35]
    dist_extStein = "100"

    ys_extEuclid = [3.65, 15.51, 37.83, 71.56, 100.44,168.59, 239.67, 330.71, 440.97, 578.88]
    dist_extEuclid = "600"

    # Choose which dataset to fit
    ys = ys_fastsqrt
    dist = dist_fastsqrt

    # x-axis: experiment index 1..10 (each corresponds to an increasing digit count)
    xs = list(range(1, 11, 1))

    # Select polynomial degree by BIC (degree <= 9) under the constraint p(0)=0
    best = select_degree_by_bic(xs, ys, max_deg=6, through_origin=True)
    deg = best["deg"]
    poly = best["poly"]

    print("Fit degree:", deg)
    print("Fit polynom:", poly)

    # ---- Plotting ----
    # Convert SymPy expression to a NumPy-callable function for plotting
    x_sym = sp.Symbol("x", real=True)
    f_np = sp.lambdify(x_sym, poly, modules=["numpy"])

    x_grid = np.linspace(0, max(xs), 400)
    y_grid = f_np(x_grid)

    plt.figure()

    # Include the point (0,0) explicitly since the model is constrained to pass through it
    plt.scatter([0] + xs, [0.0] + ys, color="blue", marker="o", label="Measured data")

    # If the selected degree smaler 8, we choose not to plot the curve
    # to avoid visually endorsing a potentially overfitted model.
    if deg < 8:
        plt.plot(x_grid, y_grid, color="red", linewidth=2, label=f"Polynomial fit (degree {deg})")

    plt.xlabel("Number of digits per argument (×" + dist + ")")
    plt.ylabel("Runtime (s)")
    plt.title("")

    plt.legend()
    plt.grid(True)

    ax = plt.gca()

    # Display the fitted polynomial in the plot (rounded numerical coefficients)
    if deg < 8:
        eq = sp.latex(sp.N(poly, 5))
        ax.text(
            0.05, 0.95,
            rf"$y = {eq}$",
            transform=ax.transAxes,
            va="top",
            bbox=dict(boxstyle="round", facecolor="white", alpha=0.8)
        )


    plt.tight_layout()
    plt.savefig("fit_plot.pdf", format="pdf", bbox_inches="tight")
    print("Saved as fit_plot.pdf")