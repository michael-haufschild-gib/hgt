import GaloisForLFunctions.HTGeometry.ExponentialSeriesUniqueness
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Wiener algebra of a strip

For `σ₁ ≤ σ₂` the functions on the closed strip `σ₁ ≤ Re s ≤ σ₂` of the form
`f(s) = Σ_q c(q) q^s`, `q` over the positive reals, with
`Σ ‖c(q)‖ max(q^σ₁, q^σ₂) < ∞`, form a commutative Banach algebra `𝒲[σ₁, σ₂]`
(`StripWiener σ₁ σ₂`) under pointwise multiplication.

* **Scales** (`Scale`, `Scale.cpow`): the group of positive reals and `q^s`.
* **Weight** (`stripWeight`): `max(q^σ₁, q^σ₂)` is the supremum of `|q^s|` on the strip
  (`rpow_le_stripWeight`) and is submultiplicative (`stripWeight_mul_le`).
* **Uniqueness** (`eq_zero_of_expansion_eq_zero`): the coefficients are determined by the function
  on one vertical line, by the Bohr mean value.
* **Products** (`convolve`, `expansion_convolve`, `wsummable_convolve`): the product of two expansions is the
  expansion of the convolution of the coefficients over the group, and the weighted norm is
  submultiplicative.
* **Banach algebra** (`StripWiener`, `isometryLp`): the weighted coefficients identify the algebra
  isometrically with `ℓ¹` of the group of scales; `‖1‖ = 1`.
* **Point masses** (`pointMass`, `hasSum_pointMass`): `δ_q(s) = q^s`, `δ_q δ_r = δ_{qr}`,
  `‖δ_q‖ = max(q^σ₁, q^σ₂)`, and `f = Σ c(q) δ_q` in norm.

Dirichlet series are the expansions supported on the scales `1/n`, exponential polynomials those
of finite support. The inverse of an expansion that has zeros on both sides of the strip needs
scales of both sizes, which is why a group and not the monoid of the integers is the index set.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- The group of positive reals: the scales of an expansion. -/
abbrev Scale : Type := {a : ℝ // 0 < a}

namespace Scale

/-- A scale as a real number. -/
def toReal (q : Scale) : ℝ := q.1

theorem toReal_pos (q : Scale) : 0 < q.toReal := q.2

theorem toReal_mul (q r : Scale) : (q * r).toReal = q.toReal * r.toReal := rfl

theorem toReal_one : (1 : Scale).toReal = 1 := rfl

theorem toReal_injective : Function.Injective toReal := fun _ _ h => Subtype.ext h

/-- `q^s` for a scale `q`. -/
def cpow (q : Scale) (s : ℂ) : ℂ := (q.toReal : ℂ) ^ s

theorem cpow_mul (q r : Scale) (s : ℂ) : (q * r).cpow s = q.cpow s * r.cpow s := by
  unfold cpow
  rw [toReal_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg q.toReal_pos.le
    r.toReal_pos.le]

theorem one_cpow (s : ℂ) : (1 : Scale).cpow s = 1 := by
  unfold cpow
  rw [toReal_one, Complex.ofReal_one, Complex.one_cpow]

theorem norm_cpow (q : Scale) (s : ℂ) : ‖q.cpow s‖ = q.toReal ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos q.toReal_pos s

/-- On a vertical line `q^{σ + it} = q^σ e^{i t log q}`. -/
theorem cpow_line (q : Scale) (σ t : ℝ) :
    q.cpow ((σ : ℂ) + (t : ℂ) * Complex.I) =
      ((q.toReal ^ σ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((Real.log q.toReal : ℝ) : ℂ) * (t : ℂ)) := by
  have hne : (q.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr q.toReal_pos.ne'
  unfold cpow
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log q.toReal_pos.le,
    Real.rpow_def_of_pos q.toReal_pos, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Scale

variable {σ₁ σ₂ : ℝ}

/-! ### The weight of a strip -/

/-- The weight of the closed strip `σ₁ ≤ Re s ≤ σ₂` at the scale `q`: `max(q^σ₁, q^σ₂)`. -/
def stripWeight (σ₁ σ₂ : ℝ) (q : Scale) : ℝ := max (q.toReal ^ σ₁) (q.toReal ^ σ₂)

theorem stripWeight_pos (σ₁ σ₂ : ℝ) (q : Scale) : 0 < stripWeight σ₁ σ₂ q :=
  lt_max_of_lt_left (Real.rpow_pos_of_pos q.toReal_pos _)

theorem stripWeight_one (σ₁ σ₂ : ℝ) : stripWeight σ₁ σ₂ 1 = 1 := by
  unfold stripWeight
  rw [Scale.toReal_one, Real.one_rpow, Real.one_rpow, max_self]

/-- The weight is submultiplicative. -/
theorem stripWeight_mul_le (σ₁ σ₂ : ℝ) (q r : Scale) :
    stripWeight σ₁ σ₂ (q * r) ≤ stripWeight σ₁ σ₂ q * stripWeight σ₁ σ₂ r := by
  have hq := q.toReal_pos
  have hr := r.toReal_pos
  unfold stripWeight
  rw [Scale.toReal_mul, Real.mul_rpow hq.le hr.le, Real.mul_rpow hq.le hr.le]
  exact max_le
    (mul_le_mul (le_max_left _ _) (le_max_left _ _) (Real.rpow_nonneg hr.le _)
      ((Real.rpow_nonneg hq.le _).trans (le_max_left _ _)))
    (mul_le_mul (le_max_right _ _) (le_max_right _ _) (Real.rpow_nonneg hr.le _)
      ((Real.rpow_nonneg hq.le _).trans (le_max_right _ _)))

/-- The weight dominates `q^σ` for every `σ` of the strip. -/
theorem rpow_le_stripWeight {σ : ℝ} (h₁ : σ₁ ≤ σ) (h₂ : σ ≤ σ₂) (q : Scale) :
    q.toReal ^ σ ≤ stripWeight σ₁ σ₂ q := by
  rcases le_total q.toReal 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge q.toReal_pos h h₁).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_max_right _ _)

/-! ### Expansions -/

/-- Absolute convergence on the strip: `Σ ‖c(q)‖ max(q^σ₁, q^σ₂) < ∞`. -/
def WSummable (σ₁ σ₂ : ℝ) (c : Scale → ℂ) : Prop :=
  Summable fun q => ‖c q‖ * stripWeight σ₁ σ₂ q

/-- The expansion `Σ_q c(q) q^s`. -/
def expansion (c : Scale → ℂ) (s : ℂ) : ℂ := ∑' q, c q * q.cpow s

theorem norm_term_le (c : Scale → ℂ) {s : ℂ} (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) (q : Scale) :
    ‖c q * q.cpow s‖ ≤ ‖c q‖ * stripWeight σ₁ σ₂ q := by
  rw [norm_mul, Scale.norm_cpow]
  exact mul_le_mul_of_nonneg_left (rpow_le_stripWeight h₁ h₂ q) (norm_nonneg _)

theorem WSummable.summable_norm_term {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) {s : ℂ}
    (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) : Summable fun q => ‖c q * q.cpow s‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le c h₁ h₂) hc

theorem WSummable.summable_term {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) {s : ℂ}
    (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) : Summable fun q => c q * q.cpow s :=
  (hc.summable_norm_term h₁ h₂).of_norm

/-- The expansion is bounded by the weighted norm on the strip. -/
theorem WSummable.norm_expansion_le {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) {s : ℂ}
    (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    ‖expansion c s‖ ≤ ∑' q, ‖c q‖ * stripWeight σ₁ σ₂ q :=
  tsum_of_norm_bounded hc.hasSum (norm_term_le c h₁ h₂)

theorem WSummable.add {c d : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) (hd : WSummable σ₁ σ₂ d) :
    WSummable σ₁ σ₂ (c + d) :=
  Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le)
    (fun q => by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (stripWeight_pos σ₁ σ₂ q).le)
    (Summable.add hc hd)

theorem WSummable.smul {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) (z : ℂ) :
    WSummable σ₁ σ₂ (z • c) := by
  refine (Summable.mul_left ‖z‖ hc).congr fun q => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]

theorem WSummable.neg {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) : WSummable σ₁ σ₂ (-c) := by
  refine hc.congr fun q => ?_
  rw [Pi.neg_apply, norm_neg]

theorem wsummable_zero : WSummable σ₁ σ₂ 0 := by
  refine summable_zero.congr fun q => ?_
  rw [Pi.zero_apply, norm_zero, zero_mul]

theorem wsummable_single (q : Scale) (z : ℂ) : WSummable σ₁ σ₂ (Pi.single q z) := by
  refine summable_of_ne_finset_zero (s := {q}) fun r hr => ?_
  rw [Finset.mem_singleton] at hr
  rw [Pi.single_eq_of_ne hr, norm_zero, zero_mul]

theorem expansion_add {c d : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) (hd : WSummable σ₁ σ₂ d)
    {s : ℂ} (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    expansion (c + d) s = expansion c s + expansion d s := by
  unfold expansion
  rw [← (hc.summable_term h₁ h₂).tsum_add (hd.summable_term h₁ h₂)]
  exact tsum_congr fun q => by rw [Pi.add_apply, add_mul]

theorem expansion_smul (z : ℂ) (c : Scale → ℂ) (s : ℂ) :
    expansion (z • c) s = z * expansion c s := by
  unfold expansion
  rw [← tsum_mul_left]
  exact tsum_congr fun q => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem expansion_zero (s : ℂ) : expansion 0 s = 0 := by
  unfold expansion
  simp

theorem expansion_single (q : Scale) (z : ℂ) (s : ℂ) :
    expansion (Pi.single q z) s = z * q.cpow s := by
  unfold expansion
  rw [tsum_eq_single q fun r hr => by rw [Pi.single_eq_of_ne hr, zero_mul], Pi.single_eq_same]

/-! ### Uniqueness of the coefficients -/

/-- **The coefficients are determined on one line.** An absolutely convergent expansion that
vanishes on the strip has zero coefficients: on the line `Re s = σ₁` it is an absolutely
convergent series of exponentials with the distinct frequencies `log q`. -/
theorem eq_zero_of_expansion_eq_zero (h12 : σ₁ ≤ σ₂) {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c)
    (h : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → expansion c s = 0) : c = 0 := by
  -- the support is countable: the mean value is taken over it
  have hcount : (Function.support c).Countable :=
    hc.countable_support.mono fun q hq =>
      mul_ne_zero (norm_ne_zero_iff.mpr hq) (stripWeight_pos σ₁ σ₂ q).ne'
  haveI : Countable (Function.support c) := hcount.to_subtype
  have hinj : Function.Injective fun q : Function.support c =>
      Real.log (q : Scale).toReal := fun q r hqr =>
    Subtype.ext (Scale.toReal_injective
      (Real.log_injOn_pos (q : Scale).toReal_pos (r : Scale).toReal_pos hqr))
  have hre : ∀ t : ℝ, ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = σ₁ := fun t => by simp
  have hsum : Summable fun q : Scale => ‖c q * ((q.toReal ^ σ₁ : ℝ) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) hc
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg q.toReal_pos.le _)]
    exact mul_le_mul_of_nonneg_left (rpow_le_stripWeight le_rfl h12 q) (norm_nonneg _)
  have hzero : ∀ t : ℝ, ∑' q : Function.support c,
      c q * ((((q : Scale).toReal ^ σ₁ : ℝ)) : ℂ) *
        Complex.exp (Complex.I * ((Real.log (q : Scale).toReal : ℝ) : ℂ) * (t : ℂ)) = 0 := by
    intro t
    have h0 := h ((σ₁ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]) (by rw [hre]; exact h12)
    have e := tsum_subtype (Function.support c) fun q : Scale =>
      c q * ((q.toReal ^ σ₁ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((Real.log q.toReal : ℝ) : ℂ) * (t : ℂ))
    refine e.trans ?_
    rw [← h0]
    unfold expansion
    refine tsum_congr fun q => ?_
    by_cases hq : q ∈ Function.support c
    · rw [Set.indicator_of_mem hq, Scale.cpow_line, mul_assoc]
    · rw [Set.indicator_of_notMem hq, Function.notMem_support.mp hq, zero_mul]
  funext q
  show c q = 0
  by_contra hq
  have hq' := HTGeometry.coeff_eq_zero_of_tsum_cis_eq_zero hinj (hsum.subtype _) hzero ⟨q, hq⟩
  rcases mul_eq_zero.mp hq' with h0 | h0
  · exact hq h0
  · exact absurd (Complex.ofReal_eq_zero.mp h0) (Real.rpow_pos_of_pos q.toReal_pos _).ne'

/-! ### Products -/

/-- The shear `(m, q) ↦ (q, q⁻¹ m)` of the square of the group. -/
def shear : Scale × Scale ≃ Scale × Scale where
  toFun z := (z.2, z.2⁻¹ * z.1)
  invFun z := (z.1 * z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- **Summation along the fibres of the product.** A summable family on the square of the group
sums to the sum over `m` of its sums over the pairs with product `m`. -/
theorem hasSum_fibres {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {G : Scale × Scale → E} (hG : Summable G) :
    HasSum (fun m => ∑' q, G (q, q⁻¹ * m)) (∑' z, G z) ∧
      ∀ m, Summable fun q => G (q, q⁻¹ * m) := by
  have hG' : Summable (G ∘ shear) := (shear.summable_iff).mpr hG
  have hsum : (∑' z, (G ∘ shear) z) = ∑' z, G z := shear.tsum_eq G
  refine ⟨?_, fun m => hG'.prod_factor m⟩
  have h := hG'.hasSum.prod_fiberwise fun m => (hG'.prod_factor m).hasSum
  rwa [hsum] at h

/-- The convolution of two coefficient families over the group: `Σ_q c(q) d(q⁻¹ m)`. -/
def convolve (c d : Scale → ℂ) (m : Scale) : ℂ := ∑' q, c q * d (q⁻¹ * m)

/-- **The weighted norm is submultiplicative.** -/
theorem wsummable_convolve {c d : Scale → ℂ} (hc : WSummable σ₁ σ₂ c)
    (hd : WSummable σ₁ σ₂ d) :
    WSummable σ₁ σ₂ (convolve c d) ∧
      (∑' m, ‖convolve c d m‖ * stripWeight σ₁ σ₂ m) ≤
        (∑' q, ‖c q‖ * stripWeight σ₁ σ₂ q) * ∑' q, ‖d q‖ * stripWeight σ₁ σ₂ q := by
  set G : Scale × Scale → ℝ := fun z =>
    (‖c z.1‖ * stripWeight σ₁ σ₂ z.1) * (‖d z.2‖ * stripWeight σ₁ σ₂ z.2) with hGdef
  have hnn : ∀ q, 0 ≤ ‖c q‖ * stripWeight σ₁ σ₂ q := fun q =>
    mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le
  have hnn' : ∀ q, 0 ≤ ‖d q‖ * stripWeight σ₁ σ₂ q := fun q =>
    mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le
  have hG : Summable G := Summable.mul_of_nonneg hc hd hnn hnn'
  obtain ⟨hfib, hinner⟩ := hasSum_fibres hG
  have htot : (∑' z, G z) =
      (∑' q, ‖c q‖ * stripWeight σ₁ σ₂ q) * ∑' q, ‖d q‖ * stripWeight σ₁ σ₂ q :=
    (hc.tsum_mul_tsum hd hG).symm
  -- the terms of the convolution are dominated by the fibre of `G`
  have hterm : ∀ m q, ‖c q * d (q⁻¹ * m)‖ * stripWeight σ₁ σ₂ m ≤ G (q, q⁻¹ * m) := by
    intro m q
    have hw : stripWeight σ₁ σ₂ m ≤ stripWeight σ₁ σ₂ q * stripWeight σ₁ σ₂ (q⁻¹ * m) := by
      have h := stripWeight_mul_le σ₁ σ₂ q (q⁻¹ * m)
      rwa [mul_inv_cancel_left] at h
    calc ‖c q * d (q⁻¹ * m)‖ * stripWeight σ₁ σ₂ m
        ≤ ‖c q * d (q⁻¹ * m)‖ * (stripWeight σ₁ σ₂ q * stripWeight σ₁ σ₂ (q⁻¹ * m)) :=
          mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = G (q, q⁻¹ * m) := by
          rw [norm_mul, hGdef]
          ring
  have hsumm : ∀ m, Summable fun q => ‖c q * d (q⁻¹ * m)‖ * stripWeight σ₁ σ₂ m := fun m =>
    Summable.of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ m).le) (hterm m) (hinner m)
  have hnorm : ∀ m, Summable fun q => ‖c q * d (q⁻¹ * m)‖ := fun m => by
    have h := (hsumm m).mul_right (stripWeight σ₁ σ₂ m)⁻¹
    refine h.congr fun q => ?_
    rw [mul_assoc, mul_inv_cancel₀ (stripWeight_pos σ₁ σ₂ m).ne', mul_one]
  have hle : ∀ m, ‖convolve c d m‖ * stripWeight σ₁ σ₂ m ≤ ∑' q, G (q, q⁻¹ * m) := by
    intro m
    calc ‖convolve c d m‖ * stripWeight σ₁ σ₂ m
        ≤ (∑' q, ‖c q * d (q⁻¹ * m)‖) * stripWeight σ₁ σ₂ m :=
          mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (hnorm m))
            (stripWeight_pos σ₁ σ₂ m).le
      _ = ∑' q, ‖c q * d (q⁻¹ * m)‖ * stripWeight σ₁ σ₂ m := tsum_mul_right.symm
      _ ≤ ∑' q, G (q, q⁻¹ * m) := (hsumm m).tsum_le_tsum (hterm m) (hinner m)
  have hws : WSummable σ₁ σ₂ (convolve c d) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ m).le) hle hfib.summable
  refine ⟨hws, ?_⟩
  rw [← htot, ← hfib.tsum_eq]
  exact hws.tsum_le_tsum hle hfib.summable

/-- **The product of two expansions is the expansion of the convolution.** -/
theorem expansion_convolve {c d : Scale → ℂ} (hc : WSummable σ₁ σ₂ c) (hd : WSummable σ₁ σ₂ d)
    {s : ℂ} (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    expansion (convolve c d) s = expansion c s * expansion d s := by
  have hG : Summable fun z : Scale × Scale => (c z.1 * z.1.cpow s) * (d z.2 * z.2.cpow s) :=
    summable_mul_of_summable_norm (f := fun q => c q * q.cpow s) (g := fun q => d q * q.cpow s)
      (hc.summable_norm_term h₁ h₂) (hd.summable_norm_term h₁ h₂)
  obtain ⟨hfib, -⟩ := hasSum_fibres hG
  have hprod : expansion c s * expansion d s =
      ∑' z : Scale × Scale, (c z.1 * z.1.cpow s) * (d z.2 * z.2.cpow s) :=
    tsum_mul_tsum_of_summable_norm (f := fun q => c q * q.cpow s) (g := fun q => d q * q.cpow s)
      (hc.summable_norm_term h₁ h₂) (hd.summable_norm_term h₁ h₂)
  have hinner : ∀ m : Scale, (∑' q, (c q * q.cpow s) * (d (q⁻¹ * m) * (q⁻¹ * m).cpow s)) =
      convolve c d m * m.cpow s := by
    intro m
    unfold convolve
    rw [← tsum_mul_right]
    refine tsum_congr fun q => ?_
    have hm : q.cpow s * (q⁻¹ * m).cpow s = m.cpow s := by
      rw [← Scale.cpow_mul, mul_inv_cancel_left]
    rw [← hm]
    ring
  rw [hprod, ← hfib.tsum_eq]
  unfold expansion
  exact tsum_congr fun m => (hinner m).symm

/-! ### The algebra -/

variable (σ₁ σ₂) in
/-- The Wiener class of the closed strip `σ₁ ≤ Re s ≤ σ₂`, as an algebra of functions on it. -/
def stripWiener : Subalgebra ℂ ({s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂} → ℂ) where
  carrier := {f | ∃ c : Scale → ℂ, WSummable σ₁ σ₂ c ∧ ∀ s, f s = expansion c s}
  mul_mem' := by
    rintro f g ⟨c, hc, hf⟩ ⟨d, hd, hg⟩
    refine ⟨convolve c d, (wsummable_convolve hc hd).1, fun s => ?_⟩
    show f s * g s = expansion (convolve c d) s
    rw [hf s, hg s, expansion_convolve hc hd s.2.1 s.2.2]
  add_mem' := by
    rintro f g ⟨c, hc, hf⟩ ⟨d, hd, hg⟩
    refine ⟨c + d, hc.add hd, fun s => ?_⟩
    show f s + g s = expansion (c + d) s
    rw [hf s, hg s, expansion_add hc hd s.2.1 s.2.2]
  algebraMap_mem' z := by
    refine ⟨Pi.single 1 z, wsummable_single 1 z, fun s => ?_⟩
    show z = expansion (Pi.single 1 z) s
    rw [expansion_single, Scale.one_cpow, mul_one]

variable (σ₁ σ₂) in
/-- The Wiener algebra `𝒲[σ₁, σ₂]` of the closed strip. -/
def StripWiener : Type := ↥(stripWiener σ₁ σ₂)

namespace StripWiener

instance : CommRing (StripWiener σ₁ σ₂) := inferInstanceAs (CommRing ↥(stripWiener σ₁ σ₂))

instance : Algebra ℂ (StripWiener σ₁ σ₂) := inferInstanceAs (Algebra ℂ ↥(stripWiener σ₁ σ₂))

/-- The value of an element at a point of the strip. -/
def eval (f : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) : ℂ := f.1 s

@[ext]
theorem ext {f g : StripWiener σ₁ σ₂} (h : ∀ s, f.eval s = g.eval s) : f = g :=
  Subtype.ext (funext h)

theorem eval_zero (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) : (0 : StripWiener σ₁ σ₂).eval s = 0 :=
  rfl

theorem eval_one (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) : (1 : StripWiener σ₁ σ₂).eval s = 1 :=
  rfl

theorem eval_add (f g : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (f + g).eval s = f.eval s + g.eval s := rfl

theorem eval_neg (f : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (-f).eval s = -f.eval s := rfl

theorem eval_sub (f g : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (f - g).eval s = f.eval s - g.eval s := rfl

theorem eval_mul (f g : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (f * g).eval s = f.eval s * g.eval s := rfl

theorem eval_smul (z : ℂ) (f : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (z • f).eval s = z * f.eval s := rfl

/-- The element with given coefficients. -/
def ofCoeff (c : Scale → ℂ) (hc : WSummable σ₁ σ₂ c) : StripWiener σ₁ σ₂ :=
  ⟨fun s => expansion c s, c, hc, fun _ => rfl⟩

theorem eval_ofCoeff (c : Scale → ℂ) (hc : WSummable σ₁ σ₂ c)
    (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) : (ofCoeff c hc).eval s = expansion c s := rfl

/-- The coefficients of an element. -/
def coeff (f : StripWiener σ₁ σ₂) : Scale → ℂ := Classical.choose f.2

theorem wsummable_coeff (f : StripWiener σ₁ σ₂) : WSummable σ₁ σ₂ f.coeff :=
  (Classical.choose_spec f.2).1

theorem eval_eq (f : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    f.eval s = expansion f.coeff s :=
  (Classical.choose_spec f.2).2 s

variable [hσ : Fact (σ₁ ≤ σ₂)]

/-- The coefficients are unique. -/
theorem coeff_eq_of {f : StripWiener σ₁ σ₂} {c : Scale → ℂ} (hc : WSummable σ₁ σ₂ c)
    (h : ∀ s, f.eval s = expansion c s) : f.coeff = c := by
  have hd : WSummable σ₁ σ₂ (f.coeff + (-1 : ℂ) • c) := f.wsummable_coeff.add (hc.smul _)
  have hz : f.coeff + (-1 : ℂ) • c = 0 := by
    refine eq_zero_of_expansion_eq_zero hσ.out hd fun s h₁ h₂ => ?_
    rw [expansion_add f.wsummable_coeff (hc.smul _) h₁ h₂, expansion_smul,
      ← f.eval_eq ⟨s, h₁, h₂⟩, h ⟨s, h₁, h₂⟩]
    ring
  funext q
  have hq := congrFun hz q
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hq
  linear_combination hq

theorem coeff_ofCoeff (c : Scale → ℂ) (hc : WSummable σ₁ σ₂ c) : (ofCoeff c hc).coeff = c :=
  coeff_eq_of hc fun _ => rfl

theorem coeff_zero : (0 : StripWiener σ₁ σ₂).coeff = 0 :=
  coeff_eq_of wsummable_zero fun s => by rw [eval_zero, expansion_zero]

theorem coeff_one : (1 : StripWiener σ₁ σ₂).coeff = Pi.single 1 1 :=
  coeff_eq_of (wsummable_single 1 1) fun s => by
    rw [eval_one, expansion_single, Scale.one_cpow, mul_one]

theorem coeff_add (f g : StripWiener σ₁ σ₂) : (f + g).coeff = f.coeff + g.coeff :=
  coeff_eq_of (f.wsummable_coeff.add g.wsummable_coeff) fun s => by
    rw [eval_add, f.eval_eq, g.eval_eq,
      expansion_add f.wsummable_coeff g.wsummable_coeff s.2.1 s.2.2]

theorem coeff_smul (z : ℂ) (f : StripWiener σ₁ σ₂) : (z • f).coeff = z • f.coeff :=
  coeff_eq_of (f.wsummable_coeff.smul z) fun s => by
    rw [eval_smul, f.eval_eq, expansion_smul]

theorem coeff_neg (f : StripWiener σ₁ σ₂) : (-f).coeff = -f.coeff :=
  coeff_eq_of f.wsummable_coeff.neg fun s => by
    rw [eval_neg, f.eval_eq, show (-f.coeff) = (-1 : ℂ) • f.coeff by
      funext q; simp, expansion_smul]
    ring

theorem coeff_sub (f g : StripWiener σ₁ σ₂) : (f - g).coeff = f.coeff - g.coeff := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, sub_eq_add_neg]

theorem coeff_mul (f g : StripWiener σ₁ σ₂) : (f * g).coeff = convolve f.coeff g.coeff :=
  coeff_eq_of (wsummable_convolve f.wsummable_coeff g.wsummable_coeff).1 fun s => by
    rw [eval_mul, f.eval_eq, g.eval_eq,
      expansion_convolve f.wsummable_coeff g.wsummable_coeff s.2.1 s.2.2]

/-! ### The norm -/

/-- The weighted `ℓ¹` norm of the coefficients. -/
def wnorm (f : StripWiener σ₁ σ₂) : ℝ := ∑' q, ‖f.coeff q‖ * stripWeight σ₁ σ₂ q

/-- The weighted norm as a group norm. -/
def groupNorm : AddGroupNorm (StripWiener σ₁ σ₂) where
  toFun := wnorm
  map_zero' := by
    unfold wnorm
    rw [coeff_zero]
    simp
  add_le' f g := by
    unfold wnorm
    rw [coeff_add, ← f.wsummable_coeff.tsum_add g.wsummable_coeff]
    refine (f.wsummable_coeff.add g.wsummable_coeff).tsum_le_tsum (fun q => ?_)
      (Summable.add f.wsummable_coeff g.wsummable_coeff)
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (stripWeight_pos σ₁ σ₂ q).le
  neg' f := by
    unfold wnorm
    rw [coeff_neg]
    simp
  eq_zero_of_map_eq_zero' f h := by
    have hz : ∀ q, ‖f.coeff q‖ * stripWeight σ₁ σ₂ q = 0 := fun q =>
      le_antisymm (h ▸ f.wsummable_coeff.le_tsum q fun r _ =>
        mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ r).le)
        (mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le)
    have hc : f.coeff = 0 := funext fun q => by
      rcases mul_eq_zero.mp (hz q) with h0 | h0
      · exact norm_eq_zero.mp h0
      · exact absurd h0 (stripWeight_pos σ₁ σ₂ q).ne'
    ext s
    rw [f.eval_eq, hc, expansion_zero, eval_zero]

instance : NormedAddCommGroup (StripWiener σ₁ σ₂) := groupNorm.toNormedAddCommGroup

theorem norm_def (f : StripWiener σ₁ σ₂) :
    ‖f‖ = ∑' q, ‖f.coeff q‖ * stripWeight σ₁ σ₂ q := rfl

instance : NormedCommRing (StripWiener σ₁ σ₂) :=
  { (inferInstance : CommRing (StripWiener σ₁ σ₂)),
    (inferInstance : NormedAddCommGroup (StripWiener σ₁ σ₂)) with
    norm_mul_le := fun f g => by
      rw [norm_def, norm_def, norm_def, coeff_mul]
      exact (wsummable_convolve f.wsummable_coeff g.wsummable_coeff).2 }

instance : NormedAlgebra ℂ (StripWiener σ₁ σ₂) :=
  { (inferInstance : Algebra ℂ (StripWiener σ₁ σ₂)) with
    norm_smul_le := fun z f => by
      rw [norm_def, norm_def, coeff_smul, ← tsum_mul_left]
      refine le_of_eq (tsum_congr fun q => ?_)
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc] }

instance : NormOneClass (StripWiener σ₁ σ₂) where
  norm_one := by
    rw [norm_def, coeff_one, tsum_eq_single 1 fun q hq => by
      rw [Pi.single_eq_of_ne hq, norm_zero, zero_mul], Pi.single_eq_same, norm_one,
      stripWeight_one, mul_one]

/-- The value at a point of the strip is bounded by the norm. -/
theorem norm_eval_le (f : StripWiener σ₁ σ₂) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    ‖f.eval s‖ ≤ ‖f‖ := by
  rw [f.eval_eq, norm_def]
  exact f.wsummable_coeff.norm_expansion_le s.2.1 s.2.2

/-! ### Completeness -/

/-- The weighted coefficients as an element of `ℓ¹`. -/
def toLp (f : StripWiener σ₁ σ₂) : lp (fun _ : Scale => ℂ) 1 :=
  ⟨fun q => f.coeff q * ((stripWeight σ₁ σ₂ q : ℝ) : ℂ), by
    refine memℓp_gen ?_
    simp only [ENNReal.toReal_one, Real.rpow_one]
    refine f.wsummable_coeff.congr fun q => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stripWeight_pos σ₁ σ₂ q).le]⟩

omit hσ in
theorem toLp_apply (f : StripWiener σ₁ σ₂) (q : Scale) :
    (toLp f : Scale → ℂ) q = f.coeff q * ((stripWeight σ₁ σ₂ q : ℝ) : ℂ) := rfl

theorem norm_lp_one (x : lp (fun _ : Scale => ℂ) 1) : ‖x‖ = ∑' q, ‖(x : Scale → ℂ) q‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

theorem norm_toLp (f : StripWiener σ₁ σ₂) : ‖toLp f‖ = ‖f‖ := by
  rw [norm_lp_one, norm_def]
  refine tsum_congr fun q => ?_
  rw [toLp_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (stripWeight_pos σ₁ σ₂ q).le]

theorem toLp_sub (f g : StripWiener σ₁ σ₂) : toLp (f - g) = toLp f - toLp g := by
  refine lp.ext (funext fun q => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, toLp_apply, toLp_apply, toLp_apply, coeff_sub, Pi.sub_apply,
    sub_mul]

omit hσ in
theorem wsummable_ofLp (x : lp (fun _ : Scale => ℂ) 1) :
    WSummable σ₁ σ₂ fun q => (x : Scale → ℂ) q / ((stripWeight σ₁ σ₂ q : ℝ) : ℂ) := by
  have hmem := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp x)
  simp only [ENNReal.toReal_one, Real.rpow_one] at hmem
  refine hmem.congr fun q => ?_
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (stripWeight_pos σ₁ σ₂ q).le,
    div_mul_cancel₀ _ (stripWeight_pos σ₁ σ₂ q).ne']

/-- The inverse of the weight isometry. -/
def ofLp (x : lp (fun _ : Scale => ℂ) 1) : StripWiener σ₁ σ₂ :=
  ofCoeff _ (wsummable_ofLp x)

theorem toLp_ofLp (x : lp (fun _ : Scale => ℂ) 1) : toLp (ofLp (σ₁ := σ₁) (σ₂ := σ₂) x) = x := by
  refine lp.ext (funext fun q => ?_)
  rw [toLp_apply, ofLp, coeff_ofCoeff, div_mul_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (stripWeight_pos σ₁ σ₂ q).ne'

omit hσ in
theorem ofLp_toLp (f : StripWiener σ₁ σ₂) : ofLp (toLp f) = f := by
  ext s
  rw [ofLp, eval_ofCoeff, f.eval_eq]
  unfold expansion
  refine tsum_congr fun q => ?_
  show (toLp f : Scale → ℂ) q / ((stripWeight σ₁ σ₂ q : ℝ) : ℂ) * q.cpow s = f.coeff q * q.cpow s
  rw [toLp_apply, mul_div_cancel_right₀ _
    (Complex.ofReal_ne_zero.mpr (stripWeight_pos σ₁ σ₂ q).ne')]

variable (σ₁ σ₂) in
/-- **The weight isometry**: `𝒲[σ₁, σ₂]` and `ℓ¹` of the group of scales are isometric. -/
def isometryLp : StripWiener σ₁ σ₂ ≃ᵢ lp (fun _ : Scale => ℂ) 1 where
  toFun := toLp
  invFun := ofLp
  left_inv := ofLp_toLp
  right_inv := toLp_ofLp
  isometry_toFun := by
    refine Isometry.of_dist_eq fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, ← toLp_sub, norm_toLp]

/-- **`𝒲[σ₁, σ₂]` is a Banach algebra.** -/
instance : CompleteSpace (StripWiener σ₁ σ₂) := by
  haveI : Fact ((1 : ENNReal) ≤ 1) := ⟨le_refl _⟩
  exact (isometryLp σ₁ σ₂).completeSpace_iff.mpr inferInstance

/-! ### Evaluation and point masses -/

/-- Evaluation at a point of the strip, as a continuous linear functional. -/
def evalCLM (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) : StripWiener σ₁ σ₂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f.eval s
      map_add' := fun f g => eval_add f g s
      map_smul' := fun z f => eval_smul z f s } 1 fun f => by
    rw [one_mul]
    exact norm_eval_le f s

theorem evalCLM_apply (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) (f : StripWiener σ₁ σ₂) :
    evalCLM s f = f.eval s := rfl

/-- The point mass `δ_q`: the function `s ↦ q^s`. -/
def pointMass (q : Scale) : StripWiener σ₁ σ₂ := ofCoeff (Pi.single q 1) (wsummable_single q 1)

omit hσ in
theorem eval_pointMass (q : Scale) (s : {s : ℂ // σ₁ ≤ s.re ∧ s.re ≤ σ₂}) :
    (pointMass q : StripWiener σ₁ σ₂).eval s = q.cpow s := by
  rw [pointMass, eval_ofCoeff, expansion_single, one_mul]

theorem coeff_pointMass (q : Scale) : (pointMass q : StripWiener σ₁ σ₂).coeff = Pi.single q 1 :=
  coeff_ofCoeff _ _

/-- `‖δ_q‖ = max(q^σ₁, q^σ₂)`. -/
theorem norm_pointMass (q : Scale) :
    ‖(pointMass q : StripWiener σ₁ σ₂)‖ = stripWeight σ₁ σ₂ q := by
  rw [norm_def, coeff_pointMass, tsum_eq_single q fun r hr => by
    rw [Pi.single_eq_of_ne hr, norm_zero, zero_mul], Pi.single_eq_same, norm_one, one_mul]

omit hσ in
theorem pointMass_one : (pointMass 1 : StripWiener σ₁ σ₂) = 1 := by
  ext s
  rw [eval_pointMass, Scale.one_cpow, eval_one]

omit hσ in
/-- **Point masses multiply**: `δ_q δ_r = δ_{qr}`. -/
theorem pointMass_mul (q r : Scale) :
    (pointMass q * pointMass r : StripWiener σ₁ σ₂) = pointMass (q * r) := by
  ext s
  rw [eval_mul, eval_pointMass, eval_pointMass, eval_pointMass, Scale.cpow_mul]

/-- **Every element is the norm-convergent series of its point masses**: `f = Σ c(q) δ_q`. -/
theorem hasSum_pointMass (f : StripWiener σ₁ σ₂) :
    HasSum (fun q => f.coeff q • (pointMass q : StripWiener σ₁ σ₂)) f := by
  have hsum : Summable fun q => f.coeff q • (pointMass q : StripWiener σ₁ σ₂) := by
    refine Summable.of_norm (f.wsummable_coeff.congr fun q => ?_)
    rw [norm_smul, norm_pointMass]
  have heq : (∑' q, f.coeff q • (pointMass q : StripWiener σ₁ σ₂)) = f := by
    ext s
    have h := (evalCLM s).hasSum hsum.hasSum
    rw [← evalCLM_apply, ← h.tsum_eq, f.eval_eq]
    unfold expansion
    refine tsum_congr fun q => ?_
    rw [evalCLM_apply, eval_smul, eval_pointMass]
  have h := hsum.hasSum
  rwa [heq] at h

end StripWiener

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
