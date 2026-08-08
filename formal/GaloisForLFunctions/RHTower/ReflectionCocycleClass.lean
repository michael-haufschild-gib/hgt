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
* For `riemannZeta` the reflection cocycle is the pure archimedean Gamma quotient
  `Gammaℝ(s)/Gammaℝ(1−s)` off the zeta zero locus and is zero exactly on that locus; its
  rate-lattice content away from zeros is zero.

Thus the functional equation enters the weld category as a class to be computed: exact-conductor
members carry the nonzero weld ray `log Q`, additive under convolution, while `ζ`'s datum is purely
archimedean.
-/
import GaloisForLFunctions.HTGeometry.WeldClassTable
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import GaloisForLFunctions.RHTower.IntegralFEPolynomial
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions.RHTower

/-! ### §1 The intrinsic reflection cocycle -/

/-- The **intrinsic reflection cocycle** of a carrier `F`: the quotient `h_F(s) = F(1−s)/F(s)`,
formed without choosing any completion.  A completion factor is exactly a trivialization of this
cocycle; its fixed-point value `h_F(1/2)` carries the completion-parity bit. -/
def reflCocycle (F : ℂ → ℂ) : ℂ → ℂ := fun s => F (1 - s) / F s

/-- **The reflection cocycle is unconditionally multiplicative in the carrier.** The cocycle of a
product is the product of the cocycles:
`h_{F·G}(s) = h_F(s)·h_G(s)`.  This is field algebra: `F(1−s)G(1−s)/(F(s)G(s))` distributes over the
two quotients. Totalized inversion makes the identity valid even at zeros, so no nonvanishing
hypothesis is needed. -/
theorem reflCocycle_mul {F G : ℂ → ℂ} {s : ℂ} :
    reflCocycle (fun z => F z * G z) s = reflCocycle F s * reflCocycle G s := by
  simp only [reflCocycle, div_eq_mul_inv, mul_inv_rev]
  ring

/-- **Bundled multiplicative reflection law.** At every point, the intrinsic reflection cocycle is
a zero-preserving monoid homomorphism from carriers under pointwise multiplication to complex
values. This packages the unconditional product law and discharges the multiplicativity interface
needed by downstream character and kernel arguments. -/
def reflCocycleMonoidWithZeroHom (s : ℂ) : (ℂ → ℂ) →*₀ ℂ where
  toFun F := reflCocycle F s
  map_one' := by simp [reflCocycle]
  map_mul' F G := by
    simpa only [Pi.mul_apply] using! (reflCocycle_mul (F := F) (G := G) (s := s))
  map_zero' := by simp [reflCocycle]

/-- **The reflection cocycle sends carrier quotients to cocycle quotients unconditionally.**
`h_(F/G)(s) = h_F(s) / h_G(s)` holds even at zeros, by the totalized inverse laws in the ambient
field. Together with `reflCocycle_mul`, this makes the reflection cocycle an exact multiplicative
and quotient-compatible operation on all carriers. -/
theorem reflCocycle_div {F G : ℂ → ℂ} {s : ℂ} :
    reflCocycle (fun z ↦ F z / G z) s =
      reflCocycle F s / reflCocycle G s := by
  simp only [reflCocycle, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- **Unconditional value-reflection law.** Reflecting the argument of an intrinsic reflection
cocycle inverts its value:
`h_F(1-s) = h_F(s)⁻¹`. This is stronger than the usual nonvanishing cocycle identity
`h_F(s) h_F(1-s) = 1`: it remains exact at every zero because inversion is totalized in `ℂ`. -/
theorem reflCocycle_one_sub (F : ℂ → ℂ) (s : ℂ) :
    reflCocycle F (1 - s) = (reflCocycle F s)⁻¹ := by
  simp only [reflCocycle, show (1 : ℂ) - (1 - s) = s from by ring,
    div_eq_mul_inv, mul_inv_rev, inv_inv]

/-- **Exact cocycle-zero support law.** For an arbitrary carrier, the totalized reflection
cocycle vanishes exactly when either endpoint of the reflected pair is a carrier zero. Thus its
zero set is precisely the reflection-saturation of the carrier zero set, with no functional
equation or nonvanishing premise. -/
theorem reflCocycle_eq_zero_iff {F : ℂ → ℂ} {s : ℂ} :
    reflCocycle F s = 0 ↔ F (1 - s) = 0 ∨ F s = 0 := by
  exact (div_eq_zero_iff : F (1 - s) / F s = 0 ↔ _)

/-- **Exact reflection-law evaluation, including zeros.** If a carrier obeys a pointwise
reflection law with multiplier `H`, then its intrinsic cocycle is `H` precisely off the carrier
zero locus and is zero on that locus. This is the unconditional normal form behind every
functional-equation cocycle calculation; no multiplier or carrier nonvanishing premise is needed. -/
theorem reflCocycle_eq_ite_of_reflection
    {F H : ℂ → ℂ} {s : ℂ} (hF : F (1 - s) = H s * F s) :
    reflCocycle F s = if F s = 0 then 0 else H s := by
  rw [reflCocycle, hF]
  by_cases hFs : F s = 0 <;> simp [hFs]

/-- **Exact zero reflection interface.** Under a nonzero pointwise reflection multiplier, the
intrinsic cocycle vanishes exactly on the unreflected carrier zero locus. -/
theorem reflCocycle_eq_zero_iff_of_reflection
    {F H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s) (hH : H s ≠ 0) :
    reflCocycle F s = 0 ↔ F s = 0 := by
  rw [reflCocycle_eq_zero_iff, hF]
  simp [hH]

/-- **Unconditional exact pointwise kernel law.** The reflection cocycle is trivial exactly when
the carrier is nonzero at the unreflected point and its two reflected values agree. Thus the
nonvanishing premise in the usual kernel statement is not external data: it is forced by cocycle
triviality itself. -/
theorem reflCocycle_eq_one_iff {F : ℂ → ℂ} {s : ℂ} :
    reflCocycle F s = 1 ↔ F s ≠ 0 ∧ F (1 - s) = F s := by
  constructor
  · intro h
    have hne : F s ≠ 0 := by
      intro hzero
      simp [reflCocycle, hzero] at h
    exact ⟨hne, (div_eq_one_iff_eq hne).mp h⟩
  · rintro ⟨hne, heq⟩
    simpa only [reflCocycle] using (div_eq_one_iff_eq hne).mpr heq

/-- **Nonvanishing pointwise kernel law.** At a nonzero carrier value, the reflection cocycle is
trivial exactly when the carrier value is fixed by reflection. -/
theorem reflCocycle_eq_one_iff_reflection_fixed
    {F : ℂ → ℂ} {s : ℂ} (hFs : F s ≠ 0) :
    reflCocycle F s = 1 ↔ F (1 - s) = F s := by
  rw [reflCocycle_eq_one_iff]
  exact and_iff_right hFs

/-- **Global kernel classification without external hypotheses.** An intrinsic reflection cocycle
is identically trivial exactly when its carrier is nowhere zero and reflection-invariant. Both
parts of the usual kernel interface are therefore consequences of cocycle triviality. -/
theorem reflCocycle_eq_one_iff_reflectionInvariant (F : ℂ → ℂ) :
    (∀ s, reflCocycle F s = 1) ↔
      (∀ s, F s ≠ 0) ∧ ∀ s, F (1 - s) = F s := by
  constructor
  · intro h
    exact ⟨fun s ↦ (reflCocycle_eq_one_iff.mp (h s)).1,
      fun s ↦ (reflCocycle_eq_one_iff.mp (h s)).2⟩
  · rintro ⟨hne, hfix⟩ s
    exact reflCocycle_eq_one_iff.mpr ⟨hne s, hfix s⟩

/-- **Denominator-free pointwise fiber law.** At a point where the two carrier values are nonzero,
their reflection cocycles agree exactly when their reflected and unreflected values satisfy the
cross relation. No nonvanishing hypothesis at the reflected point is needed. -/
theorem reflCocycle_eq_iff_cross_mul
    {F G : ℂ → ℂ} {s : ℂ} (hFs : F s ≠ 0) (hGs : G s ≠ 0) :
    reflCocycle F s = reflCocycle G s ↔
      F (1 - s) * G s = G (1 - s) * F s := by
  simp only [reflCocycle]
  exact div_eq_div_iff hFs hGs

/-- **Exact pointwise fiber law.** Two nonvanishing carriers have the same reflection cocycle at
`s` exactly when their quotient is fixed by reflection there. Thus common-completion blindness is
the full kernel of the cocycle map, not merely a family of counterexamples. -/
theorem reflCocycle_eq_iff_div_reflection_fixed
    {F G : ℂ → ℂ} {s : ℂ}
    (hFs : F s ≠ 0) (hGs : G s ≠ 0) (hG1 : G (1 - s) ≠ 0) :
    reflCocycle F s = reflCocycle G s ↔
      F (1 - s) / G (1 - s) = F s / G s := by
  rw [reflCocycle_eq_iff_cross_mul hFs hGs, div_eq_div_iff hG1 hGs]
  simp only [mul_comm]

/-- **Global reflection-cocycle fiber classification.** For nowhere-vanishing carriers, equality
of the entire cocycles is equivalent to pointwise reflection invariance of their quotient. -/
theorem reflCocycle_eq_iff_div_reflectionInvariant
    {F G : ℂ → ℂ} (hF : ∀ s, F s ≠ 0) (hG : ∀ s, G s ≠ 0) :
    reflCocycle F = reflCocycle G ↔
      ∀ s, F (1 - s) / G (1 - s) = F s / G s := by
  constructor
  · intro h s
    apply (reflCocycle_eq_iff_div_reflection_fixed
      (hF s) (hG s) (hG (1 - s))).mp
    exact congrFun h s
  · intro h
    funext s
    exact (reflCocycle_eq_iff_div_reflection_fixed
      (hF s) (hG s) (hG (1 - s))).mpr (h s)

/-! ### §2 The exact-conductor collapse -/

/-- **Unconditional exact-conductor cocycle normal form.** If `f` satisfies the degree-zero
equation `f s = Q^{1−2s}·f (1−s)`, then its cocycle is the conductor power `Q^{2s−1}` off the
carrier zero locus and zero on that locus. This follows by evaluating the same functional equation
at `1-s`; no size or nonvanishing assumption on `Q` or `f s` is needed. -/
theorem reflCocycle_of_conductor_eq_ite {f : ℂ → ℂ} {Q : ℕ}
    (hfe : ∀ s, f s = (Q : ℂ) ^ (1 - 2 * s) * f (1 - s)) {s : ℂ} :
    reflCocycle f s =
      if f s = 0 then 0 else (Q : ℂ) ^ (2 * s - 1) := by
  have hreflect : f (1 - s) = (Q : ℂ) ^ (2 * s - 1) * f s := by
    simpa only [show (1 : ℂ) - 2 * (1 - s) = 2 * s - 1 by ring,
      show (1 : ℂ) - (1 - s) = s by ring] using hfe (1 - s)
  exact reflCocycle_eq_ite_of_reflection
    (F := f) (H := fun z => (Q : ℂ) ^ (2 * z - 1)) hreflect

/-- **The reflection cocycle of an exact-conductor member is a pure power.** If `f` satisfies the
degree-zero equation `f s = Q^{1−2s}·f (1−s)` and `f s ≠ 0`, then
`h_f(s) = Q^{2s−1}`. This is the nonzero branch of the unconditional piecewise normal form above;
the rate-lattice content of the cocycle is the single scale `log Q`. -/
theorem reflCocycle_of_conductor {f : ℂ → ℂ} {Q : ℕ}
    (hfe : ∀ s, f s = (Q:ℂ)^(1 - 2*s) * f (1-s)) {s : ℂ} (hfs : f s ≠ 0) :
    reflCocycle f s = (Q:ℂ)^(2*s - 1) := by
  simpa only [if_neg hfs] using reflCocycle_of_conductor_eq_ite hfe (s := s)

/-- **Exact-conductor zero reflection.** For a nonzero natural conductor, the intrinsic cocycle
vanishes exactly at zeros of the carrier. Thus the traditional carrier nonvanishing premise is a
decidable stratum of the cocycle value, not additional functional-equation data. -/
theorem reflCocycle_of_conductor_eq_zero_iff {f : ℂ → ℂ} {Q : ℕ} (hQ : Q ≠ 0)
    (hfe : ∀ s, f s = (Q : ℂ) ^ (1 - 2 * s) * f (1 - s)) {s : ℂ} :
    reflCocycle f s = 0 ↔ f s = 0 := by
  rw [reflCocycle_of_conductor_eq_ite hfe]
  have hQ0 : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  by_cases hfs : f s = 0
  · simp [hfs]
  · simp [hfs, (Complex.cpow_ne_zero_iff).2 (Or.inl hQ0)]

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

/-- **Zeta value reflection wherever the archimedean factors are regular.** Reflection multiplies
`ζ(s)` by the pure archimedean ratio `Gammaℝ(s)/Gammaℝ(1-s)`. The sharp hypothesis is nonvanishing
of the two `Γ_ℝ` factors: it already forces `s ≠ 0` and `s ≠ 1`, since `Γ_ℝ` vanishes at every
nonpositive even integer. No zeta nonvanishing premise is needed, and the identity holds at zeta
zeros. -/
theorem riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero {s : ℂ}
    (hΓs : Complex.Gammaℝ s ≠ 0) (hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0) :
    riemannZeta (1 - s) =
      (Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)) * riemannZeta s := by
  have hsne : s ≠ 0 := fun h =>
    hΓs (Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by rw [h]; norm_num⟩)
  have h1ne : (1 : ℂ) - s ≠ 0 := fun h =>
    hΓ1 (Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by rw [h]; norm_num⟩)
  have key : ∀ z : ℂ, z ≠ 0 → Complex.Gammaℝ z ≠ 0 →
      Complex.Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    intro z hz hΓz
    rw [riemannZeta_def_of_ne_zero hz]; field_simp
  have hfe : Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) = Complex.Gammaℝ s * riemannZeta s := by
    rw [key (1 - s) h1ne hΓ1, key s hsne hΓs, completedRiemannZeta_one_sub]
  field_simp [hΓ1]
  linear_combination hfe

/-- **Zeta-zero reflection wherever the archimedean factors are regular.** Functional-equation
reflection preserves the zeta zero locus exactly; the archimedean multiplier is a ratio of two
nonzero numbers. -/
theorem riemannZeta_one_sub_eq_zero_iff_of_Gammaℝ_ne_zero {s : ℂ}
    (hΓs : Complex.Gammaℝ s ≠ 0) (hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero hΓs hΓ1]
  simp [hΓs, hΓ1]

/-- Both archimedean factors of the reflection multiplier are nonzero as soon as neither `s` nor
`1 - s` sits on the pole ladder of `Γ_ℝ`, the nonpositive even integers. -/
theorem Gammaℝ_pair_ne_zero_off_poles {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ)) :
    Complex.Gammaℝ s ≠ 0 ∧ Complex.Gammaℝ (1 - s) ≠ 0 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact hs n (by rw [hn]; ring)
  · intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact h1s n (by rw [hn]; ring)

/-- **Zeta value reflection off the two pole ladders.** -/
theorem riemannZeta_one_sub_eq_gammaRatio_mul_off_poles {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ)) :
    riemannZeta (1 - s) =
      (Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)) * riemannZeta s :=
  riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero
    (Gammaℝ_pair_ne_zero_off_poles hs h1s).1 (Gammaℝ_pair_ne_zero_off_poles hs h1s).2

/-- **Zeta-zero reflection off the two pole ladders.** The zero locus of `ζ` is invariant under
`s ↦ 1 - s` on the whole plane minus the even ladder `-2m` and its reflection `1 + 2m`. -/
theorem riemannZeta_one_sub_eq_zero_iff_off_poles {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ)) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 :=
  riemannZeta_one_sub_eq_zero_iff_of_Gammaℝ_ne_zero
    (Gammaℝ_pair_ne_zero_off_poles hs h1s).1 (Gammaℝ_pair_ne_zero_off_poles hs h1s).2

/-- **Exact open-strip zeta value reflection.** The open strip keeps both `Γ_ℝ` factors in the
right half-plane, where they are nonvanishing. -/
theorem riemannZeta_one_sub_eq_gammaRatio_mul {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) =
      (Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)) * riemannZeta s := by
  have h1re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  exact riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero
    (Complex.Gammaℝ_ne_zero_of_re_pos h0) (Complex.Gammaℝ_ne_zero_of_re_pos h1re)

/-- **Open-strip zeta-zero reflection.** Functional-equation reflection preserves the zeta zero
locus exactly; the archimedean multiplier is nowhere zero in the open strip. -/
theorem riemannZeta_one_sub_eq_zero_iff {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  have h1re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  exact riemannZeta_one_sub_eq_zero_iff_of_Gammaℝ_ne_zero
    (Complex.Gammaℝ_ne_zero_of_re_pos h0) (Complex.Gammaℝ_ne_zero_of_re_pos h1re)

/-- **No zeros of `ζ` in the closed left half-plane beyond the trivial ones.** For `Re s ≤ 0` the
reflected point has `Re (1 - s) ≥ 1`, where `ζ` is nonvanishing by the Euler product; reflection
carries that nonvanishing back, provided `s` itself is off the pole ladder of `Γ_ℝ` — i.e. provided
`s` is neither `0` nor one of the trivial zeros `-2, -4, -6, …`. At `s = 0` the value `ζ(0) = -1/2`
settles it directly, so no hypothesis beyond nontriviality is needed. -/
theorem riemannZeta_ne_zero_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0)
    (htriv : ∀ n : ℕ, s ≠ -(2 * ((n : ℂ) + 1))) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]; norm_num
  · have h1re : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hΓs : Complex.Gammaℝ s ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      cases n with
      | zero => exact hs0 (by rw [hn]; norm_num)
      | succ k => exact htriv k (by rw [hn]; push_cast; ring)
    intro h
    exact riemannZeta_ne_zero_of_one_le_re h1re
      ((riemannZeta_one_sub_eq_zero_iff_of_Gammaℝ_ne_zero hΓs hΓ1).mpr h)

/-- **No zeros of `ζ` to the left of the strip beyond the trivial ones.** -/
theorem riemannZeta_ne_zero_of_re_lt_zero {s : ℂ} (hre : s.re < 0)
    (htriv : ∀ n : ℕ, s ≠ -(2 * ((n : ℂ) + 1))) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_re_le_zero hre.le htriv

/-- **The zero locus of `ζ` in the closed left half-plane is exactly the trivial ladder.** -/
theorem riemannZeta_eq_zero_iff_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -(2 * ((n : ℂ) + 1)) := by
  constructor
  · intro h
    by_contra hc
    exact riemannZeta_ne_zero_of_re_le_zero hre (fun n hn => hc ⟨n, hn⟩) h
  · rintro ⟨n, rfl⟩
    rw [show -(2 * ((n : ℂ) + 1)) = -2 * ((n : ℂ) + 1) by ring]
    exact riemannZeta_neg_two_mul_nat_add_one n

/-- **The zero locus of `ζ` left of the strip is exactly the trivial ladder.** -/
theorem riemannZeta_eq_zero_iff_of_re_lt_zero {s : ℂ} (hre : s.re < 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -(2 * ((n : ℂ) + 1)) :=
  riemannZeta_eq_zero_iff_of_re_le_zero hre.le

/-- **A zero of `ζ` lies strictly left of `Re s = 1`.** Euler-product nonvanishing, contraposed;
no nontriviality is needed for this edge. -/
theorem riemannZeta_zero_re_lt_one {s : ℂ} (hz : riemannZeta s = 0) : s.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hz

/-- **A zero of `ζ` is not the pole.** -/
theorem riemannZeta_zero_ne_one {s : ℂ} (hz : riemannZeta s = 0) : s ≠ 1 := by
  intro h
  have := riemannZeta_zero_re_lt_one hz
  rw [h, Complex.one_re] at this
  exact absurd this (lt_irrefl 1)

/-- **A nontrivial zero of `ζ` lies strictly right of `Re s = 0`.** -/
theorem riemannZeta_zero_re_pos {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -(2 * ((n : ℂ) + 1))) :
    0 < s.re := by
  by_contra hc
  exact riemannZeta_ne_zero_of_re_le_zero (not_lt.mp hc) htriv hz

/-- **Every nontrivial zero of `ζ` lies in the open critical strip.** The right-hand edge is the
Euler-product nonvanishing on `Re s ≥ 1`; the left-hand edge is its reflection. This is the
connector that turns the strip membership of a zero from a hypothesis into a consequence. -/
theorem riemannZeta_zero_re_mem_Ioo {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -(2 * ((n : ℂ) + 1))) :
    0 < s.re ∧ s.re < 1 :=
  ⟨riemannZeta_zero_re_pos hz htriv, riemannZeta_zero_re_lt_one hz⟩

/-- **Global dichotomy for the zero locus of `ζ`.** Every zero is either one of the trivial zeros
`-2, -4, -6, …` or lies in the open critical strip. -/
theorem riemannZeta_zero_trivial_or_mem_strip {s : ℂ} (hz : riemannZeta s = 0) :
    (∃ n : ℕ, s = -(2 * ((n : ℂ) + 1))) ∨ (0 < s.re ∧ s.re < 1) := by
  by_cases h : ∃ n : ℕ, s = -(2 * ((n : ℂ) + 1))
  · exact Or.inl h
  · exact Or.inr (riemannZeta_zero_re_mem_Ioo hz fun n hn => h ⟨n, hn⟩)

/-- **The Riemann hypothesis as a one-sided bound at every zero.** Nothing has to be excluded: the
trivial zeros lie far to the left and satisfy `Re ρ ≤ 1/2` outright, the pole is not a zero, and at a
nontrivial zero the functional equation turns the one-sided bound into equality, because `1 - ρ` is
then a zero as well and carries the same bound. -/
theorem riemannHypothesis_iff_forall_zero_re_le_half :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 / 2 := by
  constructor
  · intro hRH ρ hz
    by_cases ht : ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)
    · obtain ⟨n, rfl⟩ := ht
      rw [show (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact le_of_eq (hRH ρ hz ht (riemannZeta_zero_ne_one hz))
  · intro h ρ hz ht _
    obtain ⟨h0, h1⟩ := riemannZeta_zero_re_mem_Ioo hz fun n hn => ht ⟨n, by rw [hn]; ring⟩
    have hs : ∀ m : ℕ, ρ / 2 ≠ -(m : ℂ) := by
      intro m hc
      have he : ρ = ((-(2 * (m : ℝ)) : ℝ) : ℂ) := by push_cast; linear_combination 2 * hc
      rw [he, Complex.ofReal_re] at h0
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h1s : ∀ m : ℕ, (1 - ρ) / 2 ≠ -(m : ℂ) := by
      intro m hc
      have he : ρ = ((1 + 2 * (m : ℝ) : ℝ) : ℂ) := by push_cast; linear_combination -2 * hc
      rw [he, Complex.ofReal_re] at h1
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hle := h (1 - ρ) ((riemannZeta_one_sub_eq_zero_iff_off_poles hs h1s).mpr hz)
    rw [Complex.sub_re, Complex.one_re] at hle
    have hle2 := h ρ hz
    linarith

/-- **The Riemann hypothesis as a zero-free half-plane for `ζ`.** The `ξ`-side form of this is the
corpus's `rh_iff_xi_ne_zero_right`; this is the statement for `ζ` itself, where no completion factor
intervenes. -/
theorem riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  rw [riemannHypothesis_iff_forall_zero_re_le_half]
  constructor
  · intro h s hs hz
    exact absurd (h s hz) (not_le.mpr hs)
  · intro h ρ hz
    by_contra hc
    exact h ρ (not_le.mp hc) hz

/-- **The Riemann hypothesis as nonvanishing on the right half of the critical strip.** Outside the
strip `ζ` is nonvanishing for free, so a criterion only has to be checked where zeros can be. -/
theorem riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  refine ⟨fun h s hlo _ => h s hlo, fun h s hlo hz => ?_⟩
  rcases lt_or_ge s.re 1 with h1 | h1
  · exact h s hlo h1 hz
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz

/-- **The Riemann hypothesis as a zero-free left half of the strip.** Reflection exchanges the two
halves, so forbidding zeros on either side of the critical line is the same statement. -/
theorem riemannHypothesis_iff_riemannZeta_ne_zero_of_re_lt_half :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → riemannZeta s ≠ 0 := by
  have key : ∀ {s : ℂ}, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      riemannZeta (1 - s) = 0 := by
    intro s hz h0 h1
    have hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hc
      have he : s = ((-(2 * (m : ℝ)) : ℝ) : ℂ) := by push_cast; linear_combination 2 * hc
      rw [he, Complex.ofReal_re] at h0
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ) := by
      intro m hc
      have he : s = ((1 + 2 * (m : ℝ) : ℝ) : ℂ) := by push_cast; linear_combination -2 * hc
      rw [he, Complex.ofReal_re] at h1
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact (riemannZeta_one_sub_eq_zero_iff_off_poles hs h1s).mpr hz
  rw [riemannHypothesis_iff_forall_zero_re_le_half]
  constructor
  · intro h s h0 hhalf hz
    have hlt1 : s.re < 1 := riemannZeta_zero_re_lt_one hz
    have hrefl := h (1 - s) (key hz h0 hlt1)
    rw [Complex.sub_re, Complex.one_re] at hrefl
    linarith
  · intro h ρ hz
    by_contra hc
    have hgt : 1 / 2 < ρ.re := not_le.mp hc
    have hlt1 : ρ.re < 1 := riemannZeta_zero_re_lt_one hz
    refine h (1 - ρ) ?_ ?_ (key hz (by linarith) hlt1) <;>
      · rw [Complex.sub_re, Complex.one_re]; linarith


/-- **Unconditional open-strip zeta cocycle normal form.** The totalized reflection cocycle of
`ζ` is the archimedean Gamma ratio off the zeta zero locus and is zero exactly on that locus. This
is the sharp replacement for externally assuming `ζ(s) ≠ 0`. -/
theorem reflCocycle_zeta_eq_ite {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    reflCocycle riemannZeta s =
      if riemannZeta s = 0 then 0
      else Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) := by
  exact reflCocycle_eq_ite_of_reflection
    (F := riemannZeta)
    (H := fun z => Complex.Gammaℝ z / Complex.Gammaℝ (1 - z))
    (riemannZeta_one_sub_eq_gammaRatio_mul h0 h1)

/-- **Exact cocycle-zero/zeta-zero interface.** In the open critical strip the intrinsic
reflection cocycle vanishes exactly at zeros of `ζ`. -/
theorem reflCocycle_zeta_eq_zero_iff {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    reflCocycle riemannZeta s = 0 ↔ riemannZeta s = 0 := by
  rw [reflCocycle_eq_zero_iff, riemannZeta_one_sub_eq_zero_iff h0 h1]
  simp

/-- **The nonzero branch of zeta's pure archimedean cocycle.** Away from a zeta zero in the open
critical strip, `h_ζ(s) = Gammaℝ(s)/Gammaℝ(1-s)`. The rate-lattice content is therefore zero while
exact-conductor members carry the nonzero weld ray `log Q`. -/
theorem reflCocycle_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hζ : riemannZeta s ≠ 0) :
    reflCocycle riemannZeta s = Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) := by
  simpa only [if_neg hζ] using reflCocycle_zeta_eq_ite h0 h1

/-! ### §8 Common-completion ratio blindness -/

/-- **Exact zero-sensitive common-reflection classifier.** If two carriers obey one common
pointwise reflection multiplier, then their cocycles agree exactly in either of two situations:
the common multiplier vanishes, or the two unreflected carrier values have the same zero status.
Indeed each cocycle value is the multiplier at a nonzero carrier value and zero at a zero carrier
value. This removes all carrier nonvanishing hypotheses while recording the precise exceptional
locus rather than hiding it. -/
theorem reflCocycle_eq_iff_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s) :
    reflCocycle F s = reflCocycle G s ↔
      H s = 0 ∨ (F s = 0 ↔ G s = 0) := by
  rw [reflCocycle, reflCocycle, hF, hG]
  by_cases hH : H s = 0
  · simp [hH]
  · have hH' : (0 : ℂ) ≠ H s := Ne.symm hH
    by_cases hFs : F s = 0 <;>
      by_cases hGs : G s = 0 <;> simp [hH, hH', hFs, hGs]

/-- **Common reflection multipliers have identical cocycles without multiplier nonvanishing.** If
two carriers obey the same pointwise reflection law and their unreflected values are nonzero, then
their intrinsic reflection cocycles agree. The common multiplier may vanish: in that case both
reflected values vanish and the common cocycle value is zero. This is the sharp denominator-free
form of common-completion blindness. -/
theorem reflCocycle_eq_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s)
    (hF0 : F s ≠ 0) (hG0 : G s ≠ 0) :
    reflCocycle F s = reflCocycle G s := by
  apply (reflCocycle_eq_iff_of_common_reflection hF hG).2
  right
  simp [hF0, hG0]

/-- **Exact zero-sensitive quotient-reflection classifier.** Under a common reflection law, the
carrier quotient is reflection-fixed exactly when the multiplier is nonzero or one of the two
unreflected carrier values vanishes. A zero multiplier collapses the reflected quotient to zero,
so outside the carrier zero locus it is the precise obstruction to quotient invariance. -/
theorem ratio_one_sub_eq_iff_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s) :
    F (1 - s) / G (1 - s) = F s / G s ↔
      H s ≠ 0 ∨ F s = 0 ∨ G s = 0 := by
  rw [hF, hG]
  by_cases hH0 : H s = 0
  · rw [hH0]
    simp only [zero_mul, zero_div, ne_eq, not_true_eq_false, false_or]
    rw [eq_comm (a := 0) (b := F s / G s)]
    exact (div_eq_zero_iff :
      F s / G s = (0 : ℂ) ↔ F s = 0 ∨ G s = 0)
  · have hratio : H s * F s / (H s * G s) = F s / G s := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        H s * F s * ((G s)⁻¹ * (H s)⁻¹) =
            (H s * (H s)⁻¹) * (F s * (G s)⁻¹) := by ring
        _ = F s * (G s)⁻¹ := by rw [mul_inv_cancel₀ hH0, one_mul]
    simp [hratio, hH0]

/-- **A common nonzero reflection multiplier cancels from a quotient.** No carrier
nonvanishing premise is needed: at a zero denominator both totalized quotients vanish. This is the
algebraic mechanism behind common-completion counterexamples: dividing two arithmetic carriers
with identical conductor and archimedean data erases the entire functional-equation factor. -/
theorem ratio_one_sub_eq_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s)
    (hH : H s ≠ 0) :
    F (1 - s) / G (1 - s) = F s / G s := by
  exact (ratio_one_sub_eq_iff_of_common_reflection hF hG).2 (Or.inl hH)

/-- **Exact common-completion quotient kernel.** Under a shared reflection law, the quotient
cocycle is trivial exactly when the common multiplier and both unreflected carrier values are
nonzero. This is the sharp boundary: failure of any one factor makes the totalized quotient
cocycle zero rather than one. -/
theorem reflCocycle_div_eq_one_iff_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s) :
    reflCocycle (fun z => F z / G z) s = 1 ↔
      H s ≠ 0 ∧ F s ≠ 0 ∧ G s ≠ 0 := by
  rw [reflCocycle_eq_one_iff]
  rw [ratio_one_sub_eq_iff_of_common_reflection hF hG]
  constructor
  · rintro ⟨hQ0, hcases⟩
    have hF0 : F s ≠ 0 := by
      intro hzero
      exact hQ0 (by simp [hzero])
    have hG0 : G s ≠ 0 := by
      intro hzero
      exact hQ0 (by simp [hzero])
    exact ⟨hcases.resolve_right (by simp [hF0, hG0]), hF0, hG0⟩
  · rintro ⟨hH, hF0, hG0⟩
    exact ⟨div_ne_zero hF0 hG0, Or.inl hH⟩

/-- **The reflection cocycle is blind to nonvanishing common-completion quotients.** Under the
sharp hypotheses classified above, the intrinsic reflection cocycle of `F/G` is exactly `1`. -/
theorem reflCocycle_div_eq_one_of_common_reflection
    {F G H : ℂ → ℂ} {s : ℂ}
    (hF : F (1 - s) = H s * F s)
    (hG : G (1 - s) = H s * G s)
    (hH : H s ≠ 0) (hF0 : F s ≠ 0) (hG0 : G s ≠ 0) :
    reflCocycle (fun z => F z / G z) s = 1 := by
  exact (reflCocycle_div_eq_one_iff_of_common_reflection hF hG).2
    ⟨hH, hF0, hG0⟩

end RHTower
