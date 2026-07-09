/-
# The reflection cocycle as a computed weld class

The reflection cocycle of a carrier `F` is the intrinsic quotient `h_F(s) = F(1−s)/F(s)`.  It is
formed with no completion factor chosen, it is multiplicative in the carrier, and a completion
factor is exactly a trivialization of it.  This module makes the functional equation a *computed
weld class* rather than a postulated shape.

* For an exact-conductor member — one satisfying the degree-zero equation
  `f s = Q^{1−2s}·f (1−s)` — the reflection cocycle collapses to the pure power `Q^{2s−1}`.  Its
  rate-lattice content is the single scale `log Q`, an image under the injective weld-class
  homomorphism `weldClassHom : ℝ ↪ H²` of the weld-class table.
* Conductors multiply under Dirichlet convolution: the functional-equation datum of a product
  carries conductor `Q·R`, and `log(Q·R) = log Q + log R`, so the weld classes *add*.
* The conductor of a nondegenerate member is unique: two exact functional equations with conductors
  `Q, R` valid at one off-center point where the reflected value does not vanish force `Q = R`, via
  real-`rpow` injectivity in the base at a nonzero exponent.  Nondegeneracy is discharged for class
  members from the structure theorem: a nonzero member has finite-support integer coefficients with
  `a 1 = 1`, so along the real axis it tends to `1` and is nonzero at some large argument.
* For `riemannZeta` the reflection cocycle is a pure archimedean Gamma quotient
  `Gammaℝ(s)/Gammaℝ(1−s)`, whose rate-lattice content is zero.

Thus the functional equation enters the weld category as a class to be computed: exact-conductor
members carry the nonzero weld ray `log Q`, additive under convolution, while `ζ`'s datum is purely
archimedean.
-/
import GaloisForLFunctions.RHTower.WeldClassTable
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import GaloisForLFunctions.RHTower.IntegralFEPolynomial
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions.RHTower

/-! ### §1 The intrinsic reflection cocycle -/

/-- The **intrinsic reflection cocycle** of a carrier `F`: the quotient `h_F(s) = F(1−s)/F(s)`,
formed without choosing any completion.  A completion factor is exactly a trivialization of this
cocycle; its fixed-point value `h_F(1/2)` carries the completion-parity bit. -/
def reflCocycle (F : ℂ → ℂ) : ℂ → ℂ := fun s => F (1 - s) / F s

/-- **The reflection cocycle is multiplicative in the carrier.**  At a point where both carriers are
nonzero, the cocycle of a product is the product of the cocycles:
`h_{F·G}(s) = h_F(s)·h_G(s)`.  This is field algebra: `F(1−s)G(1−s)/(F(s)G(s))` distributes over the
two quotients. -/
theorem reflCocycle_mul {F G : ℂ → ℂ} {s : ℂ} (hF : F s ≠ 0) (hG : G s ≠ 0) :
    reflCocycle (fun z => F z * G z) s = reflCocycle F s * reflCocycle G s := by
  simp only [reflCocycle]
  field_simp

/-! ### §2 The exact-conductor collapse -/

/-- **The reflection cocycle of an exact-conductor member is a pure power.**  If `f` satisfies the
degree-zero equation `f s = Q^{1−2s}·f (1−s)` with `Q ≥ 2` and `f s ≠ 0`, then
`h_f(s) = Q^{2s−1}`.  Cross-multiplying `f(1−s)/f(s) = Q^{2s−1}` by `f s` and substituting the
functional equation, the exponents combine `Q^{2s−1}·Q^{1−2s} = Q^0 = 1`, leaving `f(1−s)`.  The
rate-lattice content of the cocycle is the single scale `log Q`. -/
theorem reflCocycle_of_conductor {f : ℂ → ℂ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hfe : ∀ s, f s = (Q:ℂ)^(1 - 2*s) * f (1-s)) {s : ℂ} (hfs : f s ≠ 0) :
    reflCocycle f s = (Q:ℂ)^(2*s - 1) := by
  have hQ0 : (Q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [reflCocycle]
  rw [div_eq_iff hfs, hfe s, ← mul_assoc, ← Complex.cpow_add _ _ hQ0,
    show (2*s - 1) + (1 - 2*s) = (0:ℂ) from by ring, Complex.cpow_zero, one_mul]

/-! ### §3 Conductors multiply under convolution -/

/-- **The functional-equation datum adds under Dirichlet convolution.**  If `f` has exact conductor
`Q` and `g` has exact conductor `R`, then the product `f·g` has exact conductor `Q·R`:
`f s·g s = (Q·R)^{1−2s}·(f(1−s)·g(1−s))`.  The conductor power splits over the natural product,
`(Q·R)^{1−2s} = Q^{1−2s}·R^{1−2s}`, since both bases are casts of nonnegative reals. -/
theorem conductor_mul {f g : ℂ → ℂ} {Q R : ℕ}
    (hfeQ : ∀ s, f s = (Q:ℂ)^(1 - 2*s) * f (1-s)) (hfeR : ∀ s, g s = (R:ℂ)^(1 - 2*s) * g (1-s)) :
    ∀ s, f s * g s = ((Q*R : ℕ):ℂ)^(1 - 2*s) * (f (1-s) * g (1-s)) := by
  intro s
  have hbridge : ((Q*R:ℕ):ℂ)^(1-2*s) = (Q:ℂ)^(1-2*s) * (R:ℂ)^(1-2*s) := by
    rw [show ((Q*R:ℕ):ℂ) = ((Q:ℝ):ℂ) * ((R:ℝ):ℂ) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg Q) (Nat.cast_nonneg R),
      Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [hfeQ s, hfeR s, hbridge]; ring

/-! ### §4 Uniqueness of the conductor -/

/-- **The conductor of a nondegenerate member is unique.**  If a single carrier `f` satisfies exact
degree-zero equations with conductors `Q` and `R` (both `≥ 2`), and there is one point `σ ≠ 1/2` at
which the reflected value `f(1−σ)` is nonzero, then `Q = R`.  Comparing the two equations at `s = σ`
and cancelling the common nonzero `f(1−σ)` gives `Q^{1−2σ} = R^{1−2σ}`; at the nonzero real exponent
`x = 1−2σ` this transfers to real `rpow`, and taking logarithms with `x ≠ 0` forces
`log Q = log R`, hence `Q = R`. -/
theorem conductor_unique {f : ℂ → ℂ} {Q R : ℕ} (hQ : 2 ≤ Q) (hR : 2 ≤ R)
    (hfeQ : ∀ s, f s = (Q:ℂ)^(1 - 2*s) * f (1-s))
    (hfeR : ∀ s, f s = (R:ℂ)^(1 - 2*s) * f (1-s))
    {σ : ℝ} (hσ : (σ:ℝ) ≠ 1/2) (hfσ : f (1 - (σ:ℂ)) ≠ 0) : Q = R := by
  have hx : (1 - 2*σ : ℝ) ≠ 0 := fun h => hσ (by linarith)
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hQ
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hR
  have hcancel : (Q:ℂ)^(1 - 2*(σ:ℂ)) = (R:ℂ)^(1 - 2*(σ:ℂ)) :=
    mul_right_cancel₀ hfσ ((hfeQ (σ:ℂ)).symm.trans (hfeR (σ:ℂ)))
  rw [show (1 - 2*(σ:ℂ)) = (((1 - 2*σ : ℝ)):ℂ) by push_cast; ring] at hcancel
  have hcast : ∀ n : ℕ, (((n:ℝ) ^ (1-2*σ) : ℝ) : ℂ) = (n:ℂ) ^ (((1-2*σ:ℝ)):ℂ) := by
    intro n; rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]
  have hQR : ((Q:ℝ) ^ (1-2*σ) : ℝ) = ((R:ℝ) ^ (1-2*σ) : ℝ) := by
    have h2 : (((Q:ℝ)^(1-2*σ) : ℝ):ℂ) = (((R:ℝ)^(1-2*σ):ℝ):ℂ) := by
      rw [hcast Q, hcast R]; exact hcancel
    exact_mod_cast h2
  have hlog : (1-2*σ) * Real.log Q = (1-2*σ) * Real.log R := by
    rw [← Real.log_rpow hQpos (1-2*σ), ← Real.log_rpow hRpos (1-2*σ), hQR]
  have hlogQR : Real.log Q = Real.log R := mul_left_cancel₀ hx hlog
  have hfin : (Q:ℝ) = (R:ℝ) := by rw [← Real.exp_log hQpos, ← Real.exp_log hRpos, hlogQR]
  exact_mod_cast hfin

/-! ### §5 Nondegeneracy for class members -/

/-- **A nonzero class member has an off-center non-vanishing reflected value.**  For a member `f` of
the integral multiplicative functional-equation class that is not identically zero, there is a real
`σ ≠ 1/2` with `f(1−σ) ≠ 0`.  By the structure theorem the member is the `L`-series of an
integer-valued multiplicative arithmetic function with finite support and `a 1 = 1`.  Splitting off
the `n = 1` term, `f(τ) = 1 + Σ_{n∈supp, n≥2} a_n n^{−τ}`, and each tail term is bounded by
`‖a_n‖·2^{−τ}`; choosing `τ` large makes the finite tail have norm `< 1`, so `f(τ) ≠ 0`.  Setting
`σ = 1−τ` (with `τ > 1/2`) gives `f(1−σ) = f(τ) ≠ 0` and `σ ≠ 1/2`. -/
theorem exists_offcenter_nonvanishing {f : ℂ → ℂ}
    (hf : IntegralMultiplicativeFEClass f) (hne : ∃ s, f s ≠ 0) :
    ∃ σ : ℝ, (σ:ℝ) ≠ 1/2 ∧ f (1 - (σ:ℂ)) ≠ 0 := by
  rcases integralMultiplicativeFEClass_finite_or_zero hf with hz | ⟨a, hmul, _hint, hrep, hfin⟩
  · obtain ⟨s0, hs0⟩ := hne; exact absurd (hz s0) hs0
  set S : Finset ℕ := hfin.toFinset with hS
  have hmemS : ∀ n, n ∈ S ↔ a n ≠ 0 := by
    intro n; simp only [hS, Set.Finite.mem_toFinset, Function.mem_support]
  have ha1 : a 1 = 1 := hmul.map_one
  have h1S : (1:ℕ) ∈ S := (hmemS 1).mpr (by rw [ha1]; norm_num)
  have h0S : (0:ℕ) ∉ S := fun h => ((hmemS 0).mp h) a.map_zero
  have hterm_out : ∀ (s : ℂ) (n : ℕ), n ∉ S → LSeries.term (fun n => a n) s n = 0 := by
    intro s n hn
    rcases eq_or_ne n 0 with h0 | h0
    · rw [h0, LSeries.term_zero]
    · have han : a n = 0 := not_not.mp (mt (hmemS n).mpr hn)
      rw [LSeries.term_of_ne_zero h0 _ s, han, zero_div]
  have hFsum : ∀ s : ℂ, f s = ∑ n ∈ S, LSeries.term (fun n => a n) s n := by
    intro s
    rw [hrep s, show LSeries (fun n => a n) s = ∑' n, LSeries.term (fun n => a n) s n from rfl]
    exact tsum_eq_sum (fun n hn => hterm_out s n hn)
  have hterm1 : ∀ τ : ℝ, LSeries.term (fun n => a n) (τ:ℂ) 1 = 1 := by
    intro τ; rw [LSeries.term_of_ne_zero (one_ne_zero) _ (τ:ℂ)]; simp [ha1]
  have hnorm_tail : ∀ (τ : ℝ), 0 ≤ τ → ∀ n ∈ S, n ≠ 1 →
      ‖LSeries.term (fun n => a n) (τ:ℂ) n‖ ≤ ‖a n‖ / (2:ℝ)^τ := by
    intro τ hτ n hnS hn1
    have hn0 : n ≠ 0 := fun h => h0S (h ▸ hnS)
    have hn2 : 2 ≤ n := by omega
    rw [LSeries.norm_term_eq, if_neg hn0, Complex.ofReal_re]
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) τ)
        (Real.rpow_pos_of_pos (by norm_num) τ)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn2) hτ) (norm_nonneg _)
  set C : ℝ := ∑ n ∈ S.erase 1, ‖a n‖ with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have key : ∀ τ : ℝ, 0 ≤ τ → ‖f (τ:ℂ) - 1‖ ≤ C / (2:ℝ)^τ := by
    intro τ hτ
    have hsplit : f (τ:ℂ) = LSeries.term (fun n => a n) (τ:ℂ) 1
                    + ∑ n ∈ S.erase 1, LSeries.term (fun n => a n) (τ:ℂ) n := by
      rw [hFsum (τ:ℂ)]
      exact (Finset.add_sum_erase S (fun n => LSeries.term (fun n => a n) (τ:ℂ) n) h1S).symm
    rw [hsplit, hterm1 τ, add_sub_cancel_left]
    calc ‖∑ n ∈ S.erase 1, LSeries.term (fun n => a n) (τ:ℂ) n‖
        ≤ ∑ n ∈ S.erase 1, ‖LSeries.term (fun n => a n) (τ:ℂ) n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S.erase 1, ‖a n‖ / (2:ℝ)^τ :=
          Finset.sum_le_sum (fun n hn => hnorm_tail τ hτ n (Finset.mem_of_mem_erase hn)
            (Finset.ne_of_mem_erase hn))
      _ = C / (2:ℝ)^τ := by rw [hC, Finset.sum_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 1)
  have hCN : C < (N:ℝ) := lt_of_le_of_lt (le_max_left C 1) hN
  have h1N : (1:ℝ) < (N:ℝ) := lt_of_le_of_lt (le_max_right C 1) hN
  have hN2 : (N:ℝ) ≤ (2:ℝ)^(N:ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast N.lt_two_pow_self.le
  have h2τ : C < (2:ℝ)^(N:ℝ) := lt_of_lt_of_le hCN hN2
  have hτpos : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hden : (0:ℝ) < (2:ℝ)^(N:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt1 : ‖f ((N:ℝ):ℂ) - 1‖ < 1 :=
    lt_of_le_of_lt (key (N:ℝ) hτpos) ((div_lt_one hden).mpr h2τ)
  have hfne : f ((N:ℝ):ℂ) ≠ 0 := by
    intro h0; rw [h0] at hlt1; simp at hlt1
  refine ⟨1 - (N:ℝ), ?_, ?_⟩
  · intro h; linarith
  · show f (1 - ((1 - (N:ℝ) : ℝ):ℂ)) ≠ 0
    rw [show (1 : ℂ) - ((1 - (N:ℝ) : ℝ):ℂ) = ((N:ℝ):ℂ) by push_cast; ring]
    exact hfne

/-! ### §6 The weld-class wiring -/

/-- **Composition of conductors adds weld classes.**  For `Q, R ≥ 1`, the conductor scale of a
product `log(Q·R)` maps under the weld-class homomorphism to the sum of the individual conductor
classes: `weldClass(log(Q·R)) = weldClass(log Q) + weldClass(log R)`.  This is `log_mul` composed
with the additivity of `weldClassHom`. -/
theorem conductorClass_add {Q R : ℕ} (hQ : 1 ≤ Q) (hR : 1 ≤ R) :
    weldClassHom (Real.log (Q*R : ℕ)) = weldClassHom (Real.log Q) + weldClassHom (Real.log R) := by
  have hQ0 : ((Q:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hQ
  have hR0 : ((R:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hR
  rw [show ((Q*R:ℕ):ℝ) = ((Q:ℕ):ℝ) * ((R:ℕ):ℝ) by push_cast; ring, Real.log_mul hQ0 hR0, map_add]

/-- **An exact conductor carries a nonzero weld class.**  For `Q ≥ 2` the conductor scale `log Q` is
positive, hence nonzero, and the injective weld-class homomorphism sends it to a nonzero class:
`weldClass(log Q) ≠ 0`.  The functional-equation datum of an exact-conductor member is a genuine
(unremovable) weld. -/
theorem conductorClass_ne_zero {Q : ℕ} (hQ : 2 ≤ Q) : weldClassHom (Real.log Q) ≠ 0 := by
  intro h
  rw [weldClassHom_eq_zero_iff] at h
  exact (ne_of_gt (Real.log_pos (by exact_mod_cast hQ))) h

/-! ### §7 Zeta's reflection cocycle is purely archimedean -/

/-- **The reflection cocycle of `ζ` is a pure archimedean Gamma quotient.**  On the open critical
strip, where `ζ(s) ≠ 0` and both `Gammaℝ(s), Gammaℝ(1−s)` are nonzero,
`h_ζ(s) = Gammaℝ(s)/Gammaℝ(1−s)`.  From `Gammaℝ(z)·ζ(z) = completedRiemannZeta(z)` at `z = s` and
`z = 1−s`, together with `completedRiemannZeta(1−s) = completedRiemannZeta(s)`, one has
`Gammaℝ(1−s)·ζ(1−s) = Gammaℝ(s)·ζ(s)`; cross-multiplying gives the quotient.  The rate-lattice
content of `ζ`'s reflection cocycle is therefore zero: the functional-equation datum of `ζ` is
purely archimedean, while every exact-conductor member carries the nonzero weld ray `log Q`, additive
under Dirichlet convolution.  The functional-equation shape is a computed weld class, not an
axiom. -/
theorem reflCocycle_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s ≠ 0) :
    reflCocycle riemannZeta s = Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) := by
  have hsne : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have h1re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h1ne : (1 - s) ≠ 0 := by intro h; rw [h] at h1re; simp at h1re
  have hΓs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h1re
  have key : ∀ z : ℂ, z ≠ 0 → Complex.Gammaℝ z ≠ 0 →
      Complex.Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    intro z hz hΓz
    rw [riemannZeta_def_of_ne_zero hz]; field_simp
  have hfe : Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) = Complex.Gammaℝ s * riemannZeta s := by
    rw [key (1 - s) h1ne hΓ1, key s hsne hΓs, completedRiemannZeta_one_sub]
  simp only [reflCocycle]
  rw [div_eq_div_iff hζ hΓ1]
  linear_combination hfe

end RHTower
