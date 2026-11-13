import GaloisForLFunctions.CompactHyperbolicSurfaces.LengthSeries
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The Euler product of the Selberg zeta function

`Z_E(s) = Π_{p primitive, k ≥ 0} (1 − e^{−(s+k)ℓ_p})` converges absolutely on `Re s > 1`, where it
is holomorphic and nonvanishing (`differentiableOn_eulerZeta`, `eulerZeta_ne_zero`), and its
logarithmic derivative is the length series (`logDeriv_eulerZeta`):

  `Σ_{p,k} ℓ_p q/(1 − q) = Σ_{p,k,n} ℓ_p e^{−(n+1)(s+k)ℓ_p} = Σ_{p,n} ℓ_p e^{−(n+1)sℓ_p}/(1 − e^{−(n+1)ℓ_p})
   = Σ_{[γ] ≠ 1} ℓ₀ e^{−sℓ}/(1 − e^{−ℓ}) = Φ(s)`,

the last step through `primPowEquiv`.
-/

open MeasureTheory Set Real Filter
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

theorem one_le_div_one_sub_exp {ℓ : ℝ} (hℓ : 0 < ℓ) : 1 ≤ ℓ / (1 - exp (-ℓ)) := by
  have h1 : 0 < 1 - exp (-ℓ) := by have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hℓ); linarith
  rw [le_div_iff₀ h1, one_mul]
  have := Real.add_one_le_exp (-ℓ)
  linarith

/-- `Σ_k e^{−(σ+k)ℓ} = e^{−σℓ}/(1 − e^{−ℓ})`. -/
theorem hasSum_exp_shift {σ ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasSum (fun k : ℕ => exp (-((σ + k) * ℓ))) (exp (-(σ * ℓ)) / (1 - exp (-ℓ))) := by
  have hr : exp (-ℓ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hℓ)
  have hg := (hasSum_geometric_of_lt_one (exp_pos (-ℓ)).le hr).mul_left (exp (-(σ * ℓ)))
  rw [div_eq_mul_inv]
  refine hg.congr_fun fun k => ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  ring_nf

/-- `Σ_k e^{−(s+k)ℓ} = e^{−sℓ}/(1 − e^{−ℓ})` for complex `s`. -/
theorem hasSum_cexp_shift (s : ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasSum (fun k : ℕ => Complex.exp (-((s + k) * ℓ)))
      (Complex.exp (-(s * ℓ)) / ((1 - exp (-ℓ) : ℝ) : ℂ)) := by
  have hr : ‖Complex.exp (-(ℓ : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simpa using Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hℓ)
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (Complex.exp (-(s * ℓ)))
  have he : ((1 - exp (-ℓ) : ℝ) : ℂ) = 1 - Complex.exp (-(ℓ : ℂ)) := by
    push_cast; rfl
  rw [he, div_eq_mul_inv]
  refine hg.congr_fun fun k => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  ring_nf

namespace CompactQuotient

variable {X : CompactQuotient}

/-- The Euler factor `1 − e^{−(s+k)ℓ_p}`. -/
def eulerFactor (X : CompactQuotient) (x : X.PClass × ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-((s + x.2) * X.classLen x.1.1))

/-- **The Selberg zeta function** as an Euler product over primitive classes. -/
def eulerZeta (X : CompactQuotient) (s : ℂ) : ℂ := ∏' x : X.PClass × ℕ, X.eulerFactor x s

variable (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|)
include hhyp

theorem pLen_pos (p : X.PClass) : 0 < X.classLen p.1 := X.classLen_pos hhyp p.1.2

theorem realWeight_primPow (σ : ℝ) (p : X.PClass × ℕ) :
    X.realWeight σ (primPow hhyp p) = X.classLen p.1 * exp (-(σ * ((p.2 + 1) * X.classLen p.1))) /
      (1 - exp (-((p.2 + 1) * X.classLen p.1))) := by
  rw [realWeight, classPrimLen_primPow, classLen_primPow]

theorem summable_realWeight_primPow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : X.PClass × ℕ => X.realWeight σ (primPow hhyp p) :=
  (summable_realWeight hhyp hσ).comp_injective (primPowEquiv hhyp).injective

/-- The real Euler terms `e^{−(σ+k)ℓ_p}` are summable for `σ > 1`. -/
theorem summable_realEuler {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : X.PClass × ℕ => exp (-((σ + x.2) * X.classLen x.1.1)) := by
  have hW0 : Summable fun p : X.PClass => X.realWeight σ (primPow hhyp (p, 0)) :=
    (summable_realWeight_primPow hhyp hσ).comp_injective
      (fun p q h => (Prod.mk.inj h).1)
  have hval : ∀ p : X.PClass, X.realWeight σ (primPow hhyp (p, 0)) =
      X.classLen p.1 / (1 - exp (-X.classLen p.1)) * exp (-(σ * X.classLen p.1)) := by
    intro p
    rw [realWeight_primPow]
    simp only [Nat.cast_zero, zero_add, one_mul]
    ring
  -- primitive classes of length `< 1` are finitely many
  have hfin : {p : X.PClass | X.classLen p.1 < 1}.Finite := by
    have hev := (tendsto_order.mp hW0.tendsto_cofinite_zero).2 (exp (-σ)) (exp_pos _)
    refine (eventually_cofinite.mp hev).subset fun p hp => ?_
    simp only [mem_setOf_eq, not_lt] at hp ⊢
    rw [hval]
    have hl := pLen_pos hhyp p
    have h1 := one_le_div_one_sub_exp hl
    have h2 : exp (-σ) ≤ exp (-(σ * X.classLen p.1)) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [exp_pos (-σ)]
  have hnn : 0 ≤ fun x : X.PClass × ℕ => exp (-((σ + x.2) * X.classLen x.1.1)) :=
    fun x => (exp_pos _).le
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun p => (hasSum_exp_shift (pLen_pos hhyp p)).summable,
    ?_⟩
  simp_rw [fun p : X.PClass => (hasSum_exp_shift (σ := σ) (pLen_pos hhyp p)).tsum_eq]
  refine hW0.of_norm_bounded_eventually ?_
  refine (eventually_cofinite.mpr ?_)
  refine hfin.subset fun p hp => ?_
  simp only [mem_setOf_eq, not_le] at hp ⊢
  by_contra hge
  push_neg at hge
  apply not_le.mpr hp
  rw [hval, Real.norm_of_nonneg (div_nonneg (exp_pos _).le
    (by have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pLen_pos hhyp p)); linarith))]
  have h1 : 0 < 1 - exp (-X.classLen p.1) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pLen_pos hhyp p)); linarith
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (exp_pos _).le hge) h1.le

theorem norm_eulerTerm (s : ℂ) (x : X.PClass × ℕ) :
    ‖Complex.exp (-((s + x.2) * X.classLen x.1.1))‖ = exp (-((s.re + x.2) * X.classLen x.1.1)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem summable_eulerTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun x : X.PClass × ℕ => ‖-Complex.exp (-((s + x.2) * X.classLen x.1.1))‖ := by
  simpa only [norm_neg, norm_eulerTerm hhyp] using summable_realEuler hhyp hs

theorem eulerFactor_ne_zero {s : ℂ} (hs : 1 < s.re) (x : X.PClass × ℕ) : X.eulerFactor x s ≠ 0 := by
  rw [eulerFactor, sub_ne_zero]
  intro h
  have h1 := congrArg norm h
  rw [norm_one, norm_eulerTerm hhyp] at h1
  have hl := pLen_pos hhyp x.1
  have : exp (-((s.re + x.2) * X.classLen x.1.1)) < 1 :=
    Real.exp_lt_one_iff.mpr (by have : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _; nlinarith)
  linarith

/-- **The Euler product converges** on `Re s > 1`. -/
theorem hasProd_eulerZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun x => X.eulerFactor x s) (X.eulerZeta s) := by
  have h := Complex.multipliable_one_add_of_summable
    (f := fun x : X.PClass × ℕ => -Complex.exp (-((s + x.2) * X.classLen x.1.1)))
    (Summable.of_norm (summable_eulerTerm hhyp hs))
  simp only [← sub_eq_add_neg] at h
  exact h.hasProd

theorem eulerZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : X.eulerZeta s ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun x : X.PClass × ℕ => -Complex.exp (-((s + x.2) * X.classLen x.1.1)))
    (fun x => by rw [← sub_eq_add_neg]; exact eulerFactor_ne_zero hhyp hs x)
    (summable_eulerTerm hhyp hs)
  simpa only [← sub_eq_add_neg] using h

theorem multipliableLocallyUniformlyOn_euler {σ : ℝ} (hσ : 1 < σ) :
    MultipliableLocallyUniformlyOn (fun x : X.PClass × ℕ => X.eulerFactor x)
      {s : ℂ | σ < s.re} := by
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h := (summable_realEuler hhyp hσ).multipliableLocallyUniformlyOn_one_add hU
    (f := fun x s => -Complex.exp (-((s + x.2) * X.classLen x.1.1)))
    (Eventually.of_forall fun x s hs => by
      rw [norm_neg, norm_eulerTerm hhyp]
      have hl := pLen_pos hhyp x.1
      have : σ < s.re := hs
      exact Real.exp_le_exp.mpr (by nlinarith))
    (fun x => by fun_prop)
  simpa only [eulerFactor, ← sub_eq_add_neg] using h

/-- **`Z_E` is holomorphic on `Re s > 1`.** -/
theorem differentiableOn_eulerZeta : DifferentiableOn ℂ X.eulerZeta {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set σ := (1 + s₀.re) / 2
  have hσ : 1 < σ := by simp only [σ]; linarith
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : s₀ ∈ {s : ℂ | σ < s.re} := by show σ < s₀.re; simp only [σ]; linarith
  have hd : DifferentiableOn ℂ X.eulerZeta {s : ℂ | σ < s.re} :=
    (multipliableLocallyUniformlyOn_euler hhyp hσ).hasProdLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun _ => by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun _ _ => by unfold eulerFactor; fun_prop)) hU
  exact ((hd s₀ hmem).differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

theorem logDeriv_eulerFactor (x : X.PClass × ℕ) (s : ℂ) :
    logDeriv (X.eulerFactor x) s = X.classLen x.1.1 * Complex.exp (-((s + x.2) * X.classLen x.1.1)) /
      (1 - Complex.exp (-((s + x.2) * X.classLen x.1.1))) := by
  have hd : HasDerivAt (X.eulerFactor x) (X.classLen x.1.1 *
      Complex.exp (-((s + x.2) * X.classLen x.1.1))) s := by
    have h1 : HasDerivAt (fun s : ℂ => -((s + x.2) * X.classLen x.1.1))
        (-(X.classLen x.1.1 : ℂ)) s := by
      have := ((hasDerivAt_id s).add_const (x.2 : ℂ)).mul_const (X.classLen x.1.1 : ℂ)
      simpa using this.neg
    have h2 := (Complex.hasDerivAt_exp _).comp s h1
    have h3 := h2.const_sub 1
    convert h3 using 1
    ring
  rw [logDeriv_apply, hd.deriv]
  rfl

/-- The triple series `ℓ_p e^{−(n+1)(s+k)ℓ_p}` over `((p, k), n)`. -/
def tripleTerm (X : CompactQuotient) (s : ℂ) (y : (X.PClass × ℕ) × ℕ) : ℂ :=
  X.classLen y.1.1.1 * Complex.exp (-((y.2 + 1) * ((s + y.1.2) * X.classLen y.1.1.1)))

theorem summable_tripleTerm {s : ℂ} (hs : 1 < s.re) : Summable (X.tripleTerm s) := by
  -- reindex `((p, k), n) ↦ ((p, n), k)` and sum over `k` first
  let e : (X.PClass × ℕ) × ℕ ≃ (X.PClass × ℕ) × ℕ :=
    ⟨fun y => ((y.1.1, y.2), y.1.2), fun y => ((y.1.1, y.2), y.1.2), fun _ => rfl, fun _ => rfl⟩
  refine Summable.of_norm ?_
  rw [← e.summable_iff]
  have hnn : 0 ≤ fun y : (X.PClass × ℕ) × ℕ => ‖X.tripleTerm s (e y)‖ := fun _ => norm_nonneg _
  have hnorm : ∀ y : (X.PClass × ℕ) × ℕ, ‖X.tripleTerm s (e y)‖ =
      X.classLen y.1.1 * exp (-((s.re * (y.1.2 + 1) + y.2 * (y.1.2 + 1)) * X.classLen y.1.1)) := by
    intro y
    have hl := pLen_pos hhyp y.1.1
    simp only [tripleTerm, e, Equiv.coe_fn_mk, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hl.le, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
    ring
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun pn => ?_, ?_⟩
  · simp_rw [hnorm]
    have hl : 0 < (pn.2 + 1) * X.classLen pn.1 := by
      have := pLen_pos hhyp pn.1; positivity
    have := (hasSum_exp_shift (σ := s.re) hl).summable.mul_left (X.classLen pn.1)
    refine this.congr fun k => ?_
    congr 2
    ring
  · have hval : ∀ pn : X.PClass × ℕ, ∑' k, ‖X.tripleTerm s (e (pn, k))‖ =
        X.realWeight s.re (primPow hhyp pn) := by
      intro pn
      simp_rw [hnorm]
      have hl : 0 < (pn.2 + 1) * X.classLen pn.1 := by
        have := pLen_pos hhyp pn.1; positivity
      rw [realWeight_primPow, mul_div_assoc, ← (hasSum_exp_shift (σ := s.re) hl).tsum_eq,
        ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      congr 2
      ring
    simp_rw [hval]
    exact summable_realWeight_primPow hhyp hs

/-- **`logDeriv Z_E = Φ`** on `Re s > 1`. -/
theorem logDeriv_eulerZeta {s : ℂ} (hs : 1 < s.re) : logDeriv X.eulerZeta s = X.lengthSeries s := by
  set σ := (1 + s.re) / 2
  have hσ : 1 < σ := by simp only [σ]; linarith
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : s ∈ {s : ℂ | σ < s.re} := by show σ < s.re; simp only [σ]; linarith
  have hT := summable_tripleTerm hhyp hs
  -- the inner sums over `n`
  have hinner : ∀ x : X.PClass × ℕ, HasSum (fun n : ℕ => X.tripleTerm s (x, n))
      (logDeriv (X.eulerFactor x) s) := by
    intro x
    rw [logDeriv_eulerFactor]
    set q := Complex.exp (-((s + x.2) * X.classLen x.1.1))
    have hq : ‖q‖ < 1 := by
      rw [norm_eulerTerm hhyp]
      have hl := pLen_pos hhyp x.1
      exact Real.exp_lt_one_iff.mpr (by have : (0:ℝ) ≤ x.2 := Nat.cast_nonneg _; nlinarith)
    have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left (X.classLen x.1.1 * q)
    rw [div_eq_mul_inv]
    refine hg.congr_fun fun n => ?_
    simp only [tripleTerm, q]
    rw [mul_assoc, ← pow_succ', ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hlog : logDeriv X.eulerZeta s = ∑' x : X.PClass × ℕ, logDeriv (X.eulerFactor x) s := by
    have := logDeriv_tprod_eq_tsum hU hmem (fun x => eulerFactor_ne_zero hhyp hs x)
      (fun x => by unfold eulerFactor; fun_prop)
      ((summable_prod_of_nonneg (f := fun _ => (0 : ℝ)) le_rfl).mp
        summable_zero |> fun _ => (hT.prod_factor |> fun _ => ?_))
      (multipliableLocallyUniformlyOn_euler hhyp hσ) (eulerZeta_ne_zero hhyp hs)
    · exact this
    · exact (HasSum.summable (hT.hasSum.prod_fiberwise hinner))
  rw [hlog, ← (hT.hasSum.prod_fiberwise hinner).tsum_eq]
  -- regroup as `((p, n), k)` and sum over `k`
  let e : (X.PClass × ℕ) × ℕ ≃ (X.PClass × ℕ) × ℕ :=
    ⟨fun y => ((y.1.1, y.2), y.1.2), fun y => ((y.1.1, y.2), y.1.2), fun _ => rfl, fun _ => rfl⟩
  rw [← e.tsum_eq, Summable.tsum_prod ((e.summable_iff).mpr hT)]
  have hk : ∀ pn : X.PClass × ℕ, ∑' k, X.tripleTerm s (e (pn, k)) =
      X.classWeight s (primPow hhyp pn) := by
    intro pn
    have hl : 0 < (pn.2 + 1) * X.classLen pn.1 := by
      have := pLen_pos hhyp pn.1; positivity
    rw [classWeight, classPrimLen_primPow, classLen_primPow, mul_div_assoc]
    rw [← ((hasSum_cexp_shift (s * (pn.2 + 1)) hl).mul_left (X.classLen pn.1 : ℂ)).tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [tripleTerm, e, Equiv.coe_fn_mk]
    push_cast
    ring_nf
  simp_rw [hk]
  rw [lengthSeries, ← (primPowEquiv hhyp).tsum_eq]
  rfl

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
