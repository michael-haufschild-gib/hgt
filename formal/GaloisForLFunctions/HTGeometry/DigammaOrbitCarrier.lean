import GaloisForLFunctions.HTGeometry.DigammaRationalCarrier
import GaloisForLFunctions.HTGeometry.PolygammaShift

/-!
# The shift-orbit digamma carrier is hypertranscendental at nonzero total charge

For integer shifts `nn : Fin d → ℕ`, charges `m : Fin d → ℂ` with total charge `M = ∑ₖ mₖ ≠ 0`, the
orbit carrier `Ψ(w) = ∑ₖ mₖ ψ(w + nₖ)` is hypertranscendental.  This is the exact `d`-term,
single-`H`-orbit, nonzero-total-charge hypertranscendental statement of the signed-archimedean
orbit-charge law (§3): `Ψ = G'/G` for a single common-scale Gamma orbit product with charges `mₖ`.

Off the poles the jets collapse (`iteratedDeriv_digamma_charge_general`):
`Ψ⁽ʲ⁾(z) = M·ψ⁽ʲ⁾(z) + ∑ₖ mₖ ∑_{i<nₖ} (−1)ʲ·j!/(z+i)^{j+1}`, and the rational tail is the single
fraction `C_j/B^{j+1}` over `B = ∏_{i<N}(X+i)` (`N = maxₖ nₖ`) with `C_j` the erase-product numerator.
So `Ψ` meets the general criterion `hypertranscendental_digamma_plus_offpole_rational`.
-/

noncomputable section

open MvPolynomial HTGeometry

namespace GaloisForLFunctions

/-- **The shift-orbit digamma carrier is hypertranscendental at nonzero total charge.**
`∑ₖ mₖ ψ(w + nₖ)` satisfies no algebraic differential equation when the total charge `∑ₖ mₖ ≠ 0`. -/
theorem hypertranscendental_digamma_orbit_charge {d : ℕ} (m : Fin d → ℂ) (nn : Fin d → ℕ)
    (hM : ∑ k, m k ≠ 0) :
    Hypertranscendental (fun w => ∑ k, m k * Complex.digamma (w + (nn k : ℂ))) := by
  classical
  set N : ℕ := Finset.univ.sup nn with hN
  set B : Polynomial ℂ := ∏ i ∈ Finset.range N, (Polynomial.X + Polynomial.C (i : ℂ)) with hBdef
  have hBne : B ≠ 0 := by
    rw [hBdef, Finset.prod_ne_zero_iff]
    exact fun i _ => (Polynomial.monic_X_add_C (i : ℂ)).ne_zero
  refine hypertranscendental_digamma_plus_offpole_rational (M := ∑ k, m k) hM _ B hBne
    (fun j => ∑ k, Polynomial.C (m k) * ∑ i ∈ Finset.range (nn k),
      Polynomial.C ((-1) ^ j * (j.factorial : ℂ)) *
        ∏ i' ∈ (Finset.range N).erase i, (Polynomial.X + Polynomial.C (i' : ℂ)) ^ (j + 1)) ?_
  intro j z hz hBz
  -- each shifted digamma is `ContDiffAt` at `z`, off the poles
  have hcont : ∀ k : Fin d, ContDiffAt ℂ (j : ℕ) (fun w => Complex.digamma (w + (nn k : ℂ))) z := by
    intro k
    have hshift : ∀ p : ℕ, z + (nn k : ℂ) ≠ -(p : ℂ) := by
      intro p hp
      refine hz (p + nn k) ?_
      push_cast at hp ⊢
      linear_combination hp
    exact (contDiffAt_digamma_n (z + (nn k : ℂ)) hshift j).comp z
      (contDiffAt_id.add contDiffAt_const)
  -- linearity of the jet plus the constant shift
  have hstep1 : iteratedDeriv j (fun w => ∑ k, m k * Complex.digamma (w + (nn k : ℂ))) z
      = ∑ k, m k * iteratedDeriv j Complex.digamma (z + (nn k : ℂ)) := by
    rw [show (fun w => ∑ k, m k * Complex.digamma (w + (nn k : ℂ)))
        = ∑ k, (fun w => m k * Complex.digamma (w + (nn k : ℂ))) from by
          funext w; simp only [Finset.sum_apply]]
    rw [iteratedDeriv_sum (fun k _ => contDiffAt_const.mul (hcont k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iteratedDeriv_const_mul (m k) (hcont k)]
    congr 1
    rw [show (fun w => Complex.digamma (w + (nn k : ℂ)))
          = (fun w => Complex.digamma ((nn k : ℂ) + w)) from by funext w; rw [add_comm]]
    simp only [iteratedDeriv_comp_const_add]
    rw [add_comm (nn k : ℂ) z]
  rw [hstep1, iteratedDeriv_digamma_charge_general z hz nn m j]
  congr 1
  -- the rational tail is the single fraction `C_j / B^{j+1}`
  rw [eq_div_iff (pow_ne_zero (j + 1) hBz)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hiN : i ∈ Finset.range N :=
    Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) (Finset.le_sup (Finset.mem_univ k)))
  have hzi : z + (i : ℂ) ≠ 0 := fun h => hz i (by linear_combination h)
  have hBz_eval : B.eval z = ∏ i' ∈ Finset.range N, (z + (i' : ℂ)) := by
    rw [hBdef, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun i' _ => by simp)
  have hsplit_prod : B.eval z
      = (z + (i : ℂ)) * ∏ i' ∈ (Finset.range N).erase i, (z + (i' : ℂ)) := by
    rw [hBz_eval]
    exact (Finset.mul_prod_erase (Finset.range N) (fun i' => z + (i' : ℂ)) hiN).symm
  rw [Finset.prod_pow, hsplit_prod, mul_pow]
  field_simp

end GaloisForLFunctions

end
