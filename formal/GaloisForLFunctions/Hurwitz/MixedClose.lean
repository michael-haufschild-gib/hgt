/-
# The mixed harmonic/shifted-power close — Lemma 1's final wiring

Proves `MixedTailIndependent N s` outright (for `s ∉ ℤ`), the single unproven leaf of the all-N
row-descent chain: the harmonic coefficients of a mixed relation vanish.  Architecture
(worklog blueprint): induction on the harmonic degree bound — one finite difference lowers it
(constants die), spreading the shifted-power side by one ray; when the harmonic coefficients are
constants, one more difference gives a harmonic-free multi-ray relation, compressed and killed by
`HurwitzRayPeeling.multiRay_nat_relation_poly_kill`; the compressed conclusions telescope in the
shifted variables `ψ_t = SP(A_t ∘ (X + t))`, leaving `SP(C c) = 0` on ray 0, whence `c = 0` by
`shiftedPowerPolynomial_const_coeff_eq_zero`.
-/
import GaloisForLFunctions.Hurwitz.RayPeeling
import GaloisForLFunctions.Hurwitz.AllNTailIndependence

open Polynomial Complex Filter
open HurwitzRayPeeling HurwitzAllNTailIndependence HurwitzAllNTailIndependence.HurwitzZetaTail

namespace HurwitzMixedClose

/-- The harmonic tail difference: `H_i(n) = H_i(n−1) + n^{−(s+i)}` for `n ≥ 1`. -/
theorem harmonicTail_succ_diff {N : ℕ} (s : ℂ) (i : Fin (N + 1)) {n : ℕ} (hn : 1 ≤ n) :
    harmonicTail (N := N) s i n
      = harmonicTail (N := N) s i (n - 1) + ((n : ℂ)) ^ (-(s + (i : ℂ))) := by
  have hsplit : n = (n - 1) + 1 := by omega
  rw [hsplit]
  unfold harmonicTail
  rw [Finset.sum_range_succ]
  congr 2
  · omega
  · rw [Nat.cast_sub hn]
    push_cast
    ring

/-- A polynomial fixed by the shift `X ↦ X − 1` is constant. -/
theorem eq_C_of_comp_X_sub_one_eq {p : Polynomial ℂ}
    (h : p.comp (Polynomial.X - Polynomial.C 1) = p) : p = Polynomial.C (p.eval 0) := by
  have hstep : ∀ n : ℕ, p.eval ((n : ℂ)) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ihm =>
      have := congrArg (fun q => Polynomial.eval ((m : ℂ) + 1) q) h
      simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at this
      have hval : (m : ℂ) + 1 - 1 = (m : ℂ) := by ring
      rw [hval] at this
      have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
      rw [hcast, ← this, ihm]
  have hroots : p - Polynomial.C (p.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have himg : ((fun n : ℕ => ((n : ℂ))) '' Set.univ).Infinite :=
      Set.infinite_univ.image (fun a _ b _ hab => by exact_mod_cast hab)
    refine himg.mono ?_
    rintro v ⟨n, -, rfl⟩
    show (p - Polynomial.C (p.eval 0)).IsRoot ((n : ℂ))
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, hstep n, sub_self]
  have := sub_eq_zero.mp hroots
  exact this

end HurwitzMixedClose
