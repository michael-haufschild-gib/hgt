import GaloisForLFunctions.RHTower.XiEntireReal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite probe data does not select RH

Perturbing the centered completed function by an even real polynomial,
`Ξ_R(t) = ΞC t + R(t²)`, preserves the functional-equation parity, the Schwarz reality, the
order-one envelope, and — when `X ^ (N+1) ∣ R` — the seam jet through order `2N+1`.  The
perturbation sector `X ^ (N+1) ℝ[X]` is infinite dimensional, so any finite family of real-linear
probes, or any real subspace of finite codimension, still leaves a two-dimensional slice.

Two `ℝ`-independent real polynomials take, at some non-real point, values that span `ℂ` over `ℝ`
(`exists_nonreal_spanning`); the proof replaces the open-mapping argument by a purely algebraic
one: if the pair of values were `ℝ`-dependent at every non-real point, then the shifted Wronskian
polynomial `P(z - ic) Q(z + ic) - P(z + ic) Q(z - ic)` would vanish on the real axis for every real
shift `c`, hence identically, and evaluating along the resulting lines forces `P` and `Q` to be
proportional.

Hitting `-ΞC τ` inside that slice produces a perturbation whose perturbed function has the
non-real zero quartet `τ, -τ, conj τ, -conj τ`.  So finite probe data, finite seam jets, parity,
reality, and the order-one envelope do not force RH.
-/

noncomputable section

namespace RHTower

open Complex Polynomial

/-! ### Two independent test directions in a finite-codimension slice -/

/-- The monomial embedding `c ↦ ∑ cᵢ Xᴺ⁺¹⁺ⁱ`. -/
def monomialEmbedding (N n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] Polynomial ℝ where
  toFun c := ∑ i : Fin n, c i • X ^ (N + 1 + (i : ℕ))
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

theorem monomialEmbedding_apply (N n : ℕ) (c : Fin n → ℝ) :
    monomialEmbedding N n c = ∑ i : Fin n, c i • X ^ (N + 1 + (i : ℕ)) := rfl

theorem monomialEmbedding_coeff (N n : ℕ) (c : Fin n → ℝ) (j : Fin n) :
    (monomialEmbedding N n c).coeff (N + 1 + (j : ℕ)) = c j := by
  classical
  rw [monomialEmbedding_apply, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
    simp [Polynomial.coeff_smul, Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem monomialEmbedding_injective (N n : ℕ) :
    Function.Injective (monomialEmbedding N n) := by
  intro c d hcd
  funext j
  have := congrArg (fun p : Polynomial ℝ => p.coeff (N + 1 + (j : ℕ))) hcd
  rwa [monomialEmbedding_coeff, monomialEmbedding_coeff] at this

theorem xPow_dvd_monomialEmbedding (N n : ℕ) (c : Fin n → ℝ) :
    (X : Polynomial ℝ) ^ (N + 1) ∣ monomialEmbedding N n c := by
  rw [monomialEmbedding_apply]
  refine Finset.dvd_sum (fun i _ => ?_)
  rw [Polynomial.smul_eq_C_mul]
  exact Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _

/-- **Two independent directions survive any finite-codimension constraint.** -/
theorem exists_indep_pair_of_finiteCodim (W : Submodule ℝ (Polynomial ℝ))
    [FiniteDimensional ℝ ((Polynomial ℝ) ⧸ W)] {m : ℕ}
    (hW : Module.finrank ℝ ((Polynomial ℝ) ⧸ W) ≤ m) (N : ℕ) :
    ∃ P Q : Polynomial ℝ, P ∈ W ∧ Q ∈ W ∧
      ((X : Polynomial ℝ) ^ (N + 1) ∣ P) ∧ ((X : Polynomial ℝ) ^ (N + 1) ∣ Q) ∧
      ∀ c d : ℝ, c • P + d • Q = 0 → c = 0 ∧ d = 0 := by
  classical
  set g : (Fin (m + 2) → ℝ) →ₗ[ℝ] ((Polynomial ℝ) ⧸ W) :=
    (W.mkQ).comp (monomialEmbedding N (m + 2)) with hg
  have hrank : Module.finrank ℝ (LinearMap.range g) + Module.finrank ℝ (LinearMap.ker g) =
      m + 2 := by
    rw [LinearMap.finrank_range_add_finrank_ker g]
    simp
  have hrangele : Module.finrank ℝ (LinearMap.range g) ≤ m :=
    le_trans (Submodule.finrank_le _) hW
  have hkerge : 2 ≤ Module.finrank ℝ (LinearMap.ker g) := by omega
  have hKne : LinearMap.ker g ≠ ⊥ := by
    intro hbot
    rw [hbot] at hkerge
    simp at hkerge
  obtain ⟨c, hcK, hc0⟩ := Submodule.ne_bot_iff _ |>.mp hKne
  have hspanle : (Submodule.span ℝ {c}) ≤ LinearMap.ker g := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hcK
  have hspanrank : Module.finrank ℝ (Submodule.span ℝ ({c} : Set (Fin (m + 2) → ℝ))) = 1 :=
    finrank_span_singleton hc0
  have hlt : (Submodule.span ℝ ({c} : Set (Fin (m + 2) → ℝ))) < LinearMap.ker g :=
    Submodule.lt_of_le_of_finrank_lt_finrank hspanle (by omega)
  obtain ⟨d, hdK, hdspan⟩ := SetLike.exists_of_lt hlt
  refine ⟨monomialEmbedding N (m + 2) c, monomialEmbedding N (m + 2) d, ?_, ?_,
    xPow_dvd_monomialEmbedding _ _ _, xPow_dvd_monomialEmbedding _ _ _, ?_⟩
  · have : g c = 0 := hcK
    rwa [hg, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  · have : g d = 0 := hdK
    rwa [hg, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  · intro a b hab
    rw [← map_smul, ← map_smul, ← map_add] at hab
    have hz : a • c + b • d = 0 :=
      monomialEmbedding_injective N (m + 2) (by rwa [map_zero])
    have hb : b = 0 := by
      by_contra hbne
      refine hdspan ?_
      rw [Submodule.mem_span_singleton]
      refine ⟨-(b⁻¹ * a), ?_⟩
      have hd : b • d = -(a • c) := by linear_combination (norm := module) hz
      have hdd : d = b⁻¹ • (b • d) := by
        rw [smul_smul, inv_mul_cancel₀ hbne, one_smul]
      rw [hdd, hd, smul_neg, smul_smul, ← neg_smul]
    refine ⟨?_, hb⟩
    rw [hb, zero_smul, add_zero] at hz
    exact (smul_eq_zero.mp hz).resolve_right hc0

/-! ### A non-real point where two independent real polynomials span `ℂ` over `ℝ` -/

theorem aeval_conj_real (p : Polynomial ℝ) (z : ℂ) :
    (Polynomial.aeval ((starRingEnd ℂ) z) p : ℂ) =
      (starRingEnd ℂ) (Polynomial.aeval z p : ℂ) := by
  simpa using Polynomial.aeval_algHom_apply Complex.conjAe z p

/-- Two complex numbers whose "imaginary cross product" is nonzero span `ℂ` over `ℝ`. -/
theorem exists_real_combination {z₁ z₂ w : ℂ}
    (hD : z₁.re * z₂.im - z₁.im * z₂.re ≠ 0) :
    ∃ a b : ℝ, (a : ℂ) * z₁ + (b : ℂ) * z₂ = w := by
  refine ⟨(w.re * z₂.im - w.im * z₂.re) / (z₁.re * z₂.im - z₁.im * z₂.re),
    (z₁.re * w.im - z₁.im * w.re) / (z₁.re * z₂.im - z₁.im * z₂.re), ?_⟩
  have hre : ∀ a b : ℝ, ((a : ℂ) * z₁ + (b : ℂ) * z₂).re = a * z₁.re + b * z₂.re := by
    intro a b; simp [Complex.add_re, Complex.mul_re]
  have him : ∀ a b : ℝ, ((a : ℂ) * z₁ + (b : ℂ) * z₂).im = a * z₁.im + b * z₂.im := by
    intro a b; simp [Complex.add_im, Complex.mul_im]
  refine Complex.ext ?_ ?_
  · rw [hre, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring
  · rw [him, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring

/-- **A non-real spanning point.**  Two `ℝ`-independent real polynomials take, at some non-real
point, a pair of values that spans `ℂ` over `ℝ`. -/
theorem exists_nonreal_spanning {P Q : Polynomial ℝ}
    (hPQ : ∀ c d : ℝ, c • P + d • Q = 0 → c = 0 ∧ d = 0) :
    ∃ u : ℂ, u.im ≠ 0 ∧
      ∀ w : ℂ, ∃ a b : ℝ,
        (a : ℂ) * (Polynomial.aeval u P) + (b : ℂ) * (Polynomial.aeval u Q) = w := by
  classical
  set Pc : Polynomial ℂ := P.map (algebraMap ℝ ℂ) with hPc
  set Qc : Polynomial ℂ := Q.map (algebraMap ℝ ℂ) with hQc
  have hPcEval : ∀ z : ℂ, Pc.eval z = (Polynomial.aeval z P : ℂ) := by
    intro z; rw [hPc, Polynomial.eval_map, Polynomial.aeval_def]
  have hQcEval : ∀ z : ℂ, Qc.eval z = (Polynomial.aeval z Q : ℂ) := by
    intro z; rw [hQc, Polynomial.eval_map, Polynomial.aeval_def]
  by_contra hcon
  push Not at hcon
  have hcross : ∀ u : ℂ, u.im ≠ 0 →
      (Polynomial.aeval u P : ℂ).re * (Polynomial.aeval u Q : ℂ).im -
        (Polynomial.aeval u P : ℂ).im * (Polynomial.aeval u Q : ℂ).re = 0 := by
    intro u hu
    by_contra hD
    obtain ⟨w, hw⟩ := hcon u hu
    obtain ⟨a, b, hab⟩ := exists_real_combination (w := w) hD
    exact hw a b hab
  -- reformulate the cross product as a conjugation identity
  have hconjId : ∀ u : ℂ, u.im ≠ 0 →
      Pc.eval ((starRingEnd ℂ) u) * Qc.eval u = Pc.eval u * Qc.eval ((starRingEnd ℂ) u) := by
    intro u hu
    rw [hPcEval, hPcEval, hQcEval, hQcEval, aeval_conj_real, aeval_conj_real]
    have h := hcross u hu
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linarith [h]
  -- for each real shift the shifted Wronskian polynomial vanishes on the real axis
  have hG : ∀ c : ℝ, ∀ z : ℂ,
      Pc.eval (z - (c : ℂ) * I) * Qc.eval (z + (c : ℂ) * I) -
        Pc.eval (z + (c : ℂ) * I) * Qc.eval (z - (c : ℂ) * I) = 0 := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc
    · intro z; simp
    intro z
    set G : Polynomial ℂ :=
      (Pc.comp (X - Polynomial.C ((c : ℂ) * I))) * (Qc.comp (X + Polynomial.C ((c : ℂ) * I))) -
        (Pc.comp (X + Polynomial.C ((c : ℂ) * I))) * (Qc.comp (X - Polynomial.C ((c : ℂ) * I)))
      with hGdef
    have hGeval : ∀ y : ℂ, G.eval y =
        Pc.eval (y - (c : ℂ) * I) * Qc.eval (y + (c : ℂ) * I) -
          Pc.eval (y + (c : ℂ) * I) * Qc.eval (y - (c : ℂ) * I) := by
      intro y
      simp [hGdef, Polynomial.eval_comp]
    have hroots : (setOf G.IsRoot).Infinite := by
      refine Set.Infinite.mono (s := Set.range (fun x : ℝ => (x : ℂ))) ?_
        (Set.infinite_range_of_injective Complex.ofReal_injective)
      rintro y ⟨x, rfl⟩
      have hu : ((x : ℂ) + (c : ℂ) * I).im ≠ 0 := by
        simpa using hc
      have hconjx : (starRingEnd ℂ) ((x : ℂ) + (c : ℂ) * I) = (x : ℂ) - (c : ℂ) * I := by
        apply Complex.ext <;> simp
      have := hconjId _ hu
      rw [hconjx] at this
      show G.eval (x : ℂ) = 0
      rw [hGeval]
      linear_combination this
    have hG0 : G = 0 := Polynomial.eq_zero_of_infinite_isRoot G hroots
    have := hGeval z
    rw [hG0] at this
    simpa using this.symm
  -- hence the two polynomials are proportional
  have hprop : ∀ a : ℂ, Polynomial.C (Pc.eval a) * Qc - Polynomial.C (Qc.eval a) * Pc = 0 := by
    intro a
    set H : Polynomial ℂ := Polynomial.C (Pc.eval a) * Qc - Polynomial.C (Qc.eval a) * Pc with hH
    refine Polynomial.eq_zero_of_infinite_isRoot H ?_
    refine Set.Infinite.mono (s := Set.range (fun c : ℝ => a + 2 * (c : ℂ) * I)) ?_
      (Set.infinite_range_of_injective ?_)
    · rintro y ⟨c, rfl⟩
      have h := hG c (a + (c : ℂ) * I)
      have h1 : a + (c : ℂ) * I - (c : ℂ) * I = a := by ring
      have h2 : a + (c : ℂ) * I + (c : ℂ) * I = a + 2 * (c : ℂ) * I := by ring
      rw [h1, h2] at h
      show H.eval (a + 2 * (c : ℂ) * I) = 0
      rw [hH]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination h
    · intro c₁ c₂ hc
      have h1 : (2 : ℂ) * (c₁ : ℂ) * I = 2 * (c₂ : ℂ) * I := by
        have h2 := congrArg (fun z : ℂ => z - a) hc
        simpa using h2
      have hI : (c₁ : ℂ) = (c₂ : ℂ) := by
        have h3 : ((c₁ : ℂ) - (c₂ : ℂ)) * (2 * I) = 0 := by linear_combination h1
        rcases mul_eq_zero.mp h3 with h | h
        · linear_combination h
        · exact absurd h (by simp [Complex.ext_iff])
      exact_mod_cast hI
  -- pick a real point where `Q` does not vanish
  have hQne : Q ≠ 0 := by
    intro h0
    have hone := hPQ 0 1 (by rw [h0]; simp)
    exact one_ne_zero hone.2
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, Q.eval a₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQne (Polynomial.funext (fun x => by simpa using hall x))
  have hPa : Pc.eval ((a₀ : ℝ) : ℂ) = ((P.eval a₀ : ℝ) : ℂ) := by
    rw [hPc, Polynomial.eval_map, ← Polynomial.aeval_def,
      show (((a₀ : ℝ)) : ℂ) = algebraMap ℝ ℂ a₀ from rfl, Polynomial.aeval_algebraMap_apply]
    simp
  have hQa : Qc.eval ((a₀ : ℝ) : ℂ) = ((Q.eval a₀ : ℝ) : ℂ) := by
    rw [hQc, Polynomial.eval_map, ← Polynomial.aeval_def,
      show (((a₀ : ℝ)) : ℂ) = algebraMap ℝ ℂ a₀ from rfl, Polynomial.aeval_algebraMap_apply]
    simp
  have hkey := hprop ((a₀ : ℝ) : ℂ)
  rw [hPa, hQa] at hkey
  have hreal : Polynomial.C (P.eval a₀) * Q - Polynomial.C (Q.eval a₀) * P = 0 := by
    refine Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective ?_
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_zero, ← hPc, ← hQc]
    simpa using hkey
  have hzero : (Q.eval a₀) • P + (-(P.eval a₀)) • Q = 0 := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, map_neg]
    linear_combination -hreal
  exact ha₀ (hPQ _ _ hzero).1

/-! ### Growth envelopes -/

theorem log_two_le_envelope (t : ℂ) : Real.log 2 ≤ (1 + ‖t‖) * Real.log (2 + ‖t‖) := by
  have h1 : (1 : ℝ) ≤ 1 + ‖t‖ := by have := norm_nonneg t; linarith
  have h2 : Real.log 2 ≤ Real.log (2 + ‖t‖) :=
    Real.log_le_log (by norm_num) (by have := norm_nonneg t; linarith)
  have h3 : (0 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    le_trans (Real.log_nonneg (by norm_num)) h2
  nlinarith

theorem norm_aeval_le (R : Polynomial ℝ) (z : ℂ) :
    ‖(Polynomial.aeval z R : ℂ)‖ ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), |R.coeff i|) * (2 + ‖z‖) ^ R.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [Algebra.smul_def, norm_mul, norm_pow]
  have hcoeff : ‖(algebraMap ℝ ℂ) (R.coeff i)‖ = |R.coeff i| := by
    simp [Complex.norm_real]
  rw [hcoeff]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖z‖ ≤ 2 + ‖z‖) i) ?_
  refine pow_le_pow_right₀ (by have := norm_nonneg z; linarith) ?_
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

theorem exists_polynomial_envelope (R : Polynomial ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℂ,
      ‖(Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ)‖ ≤ Real.exp (C * (1 + ‖t‖) * Real.log (2 + ‖t‖)) := by
  set d : ℕ := R.natDegree with hd
  set A : ℝ := (∑ i ∈ Finset.range (d + 1), |R.coeff i|) + 1 with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ ∑ i ∈ Finset.range (d + 1), |R.coeff i| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  have hApos : 0 < A := by linarith
  have hlogA0 : 0 ≤ Real.log A / Real.log 2 :=
    div_nonneg (Real.log_nonneg hA1) (Real.log_nonneg (by norm_num))
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  refine ⟨2 * d + Real.log A / Real.log 2 + 1, by linarith, fun t => ?_⟩
  set X : ℝ := (1 + ‖t‖) * Real.log (2 + ‖t‖) with hX
  have hXlog : Real.log 2 ≤ X := log_two_le_envelope t
  have hX0 : 0 < X := lt_of_lt_of_le (Real.log_pos (by norm_num)) hXlog
  have hnormsq : ‖t ^ (2 : ℕ)‖ = ‖t‖ ^ (2 : ℕ) := by rw [norm_pow]
  have hstep1 : ‖(Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ)‖ ≤ A * (2 + ‖t‖ ^ (2 : ℕ)) ^ d := by
    refine le_trans (norm_aeval_le R (t ^ (2 : ℕ))) ?_
    rw [hnormsq]
    refine mul_le_mul (by rw [hA]; linarith) le_rfl (by positivity) (by linarith)
  have hlogsq : Real.log (2 + ‖t‖ ^ (2 : ℕ)) ≤ 2 * Real.log (2 + ‖t‖) := by
    have hn : 0 ≤ ‖t‖ := norm_nonneg t
    have hle : (2 : ℝ) + ‖t‖ ^ (2 : ℕ) ≤ (2 + ‖t‖) ^ (2 : ℕ) := by nlinarith
    have := Real.log_le_log (by positivity) hle
    rwa [Real.log_pow] at this
  have hstep2 : A * (2 + ‖t‖ ^ (2 : ℕ)) ^ d ≤ Real.exp (Real.log A + d * (2 * Real.log (2 + ‖t‖))) := by
    rw [Real.exp_add, Real.exp_log hApos]
    refine mul_le_mul_of_nonneg_left ?_ hApos.le
    have hpos : (0 : ℝ) < 2 + ‖t‖ ^ (2 : ℕ) := by positivity
    rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    exact mul_le_mul_of_nonneg_left hlogsq (Nat.cast_nonneg d)
  refine le_trans hstep1 (le_trans hstep2 (Real.exp_le_exp.mpr ?_))
  have hlogA : Real.log A ≤ (Real.log A / Real.log 2) * X := by
    have hlA : 0 ≤ Real.log A := Real.log_nonneg hA1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc Real.log A = (Real.log A / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (Real.log A / Real.log 2) * X :=
          mul_le_mul_of_nonneg_left hXlog (by positivity)
  have hlogle : Real.log (2 + ‖t‖) ≤ X := by
    have h1 : (1 : ℝ) ≤ 1 + ‖t‖ := by have := norm_nonneg t; linarith
    have h3 : (0 : ℝ) ≤ Real.log (2 + ‖t‖) := by
      refine Real.log_nonneg ?_
      have := norm_nonneg t; linarith
    nlinarith
  have hdterm : (d : ℝ) * (2 * Real.log (2 + ‖t‖)) ≤ 2 * d * X := by
    have := mul_le_mul_of_nonneg_left hlogle (by positivity : (0:ℝ) ≤ 2 * (d : ℝ))
    linarith
  calc Real.log A + (d : ℝ) * (2 * Real.log (2 + ‖t‖))
      ≤ (Real.log A / Real.log 2) * X + 2 * d * X := by linarith
    _ ≤ (2 * d + Real.log A / Real.log 2 + 1) * X := by nlinarith
    _ = (2 * d + Real.log A / Real.log 2 + 1) * (1 + ‖t‖) * Real.log (2 + ‖t‖) := by
        rw [hX]; ring

/-! ### The perturbed completed function -/

/-- The centered completed function perturbed by an even real polynomial. -/
def xiPerturbed (R : Polynomial ℝ) (t : ℂ) : ℂ := XiC t + (Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ)

theorem xiPerturbed_even (R : Polynomial ℝ) (t : ℂ) : xiPerturbed R (-t) = xiPerturbed R t := by
  have h : (-t) ^ (2 : ℕ) = t ^ (2 : ℕ) := by ring
  rw [xiPerturbed, xiPerturbed, XiC_even, h]

theorem xiPerturbed_conj (R : Polynomial ℝ) (t : ℂ) :
    xiPerturbed R ((starRingEnd ℂ) t) = (starRingEnd ℂ) (xiPerturbed R t) := by
  rw [xiPerturbed, xiPerturbed, XiC_conj, map_add]
  congr 1
  rw [← aeval_conj_real, map_pow]

theorem xiPerturbed_ofReal_im (R : Polynomial ℝ) (t : ℝ) : (xiPerturbed R (t : ℂ)).im = 0 := by
  have h := xiPerturbed_conj R (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem xiPerturbed_differentiable (R : Polynomial ℝ) : Differentiable ℂ (xiPerturbed R) := by
  refine XiC_differentiable.add ?_
  have h : (fun t : ℂ => (Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ)) =
      fun t : ℂ => (R.map (algebraMap ℝ ℂ)).eval (t ^ (2 : ℕ)) := by
    funext t
    rw [Polynomial.eval_map, Polynomial.aeval_def]
  rw [h]
  exact (R.map (algebraMap ℝ ℂ)).differentiable.comp (by fun_prop)

theorem xiPerturbed_sub_XiC (R : Polynomial ℝ) (t : ℂ) :
    xiPerturbed R t - XiC t = (Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ) := by
  rw [xiPerturbed]
  ring

/-- **The perturbed function has the same order-one envelope.** -/
theorem xiPerturbed_order (R : Polynomial ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℂ,
      ‖xiPerturbed R t‖ ≤ Real.exp (C * (1 + ‖t‖) * Real.log (2 + ‖t‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := XiC_order
  obtain ⟨C₂, hC₂, h₂⟩ := exists_polynomial_envelope R
  refine ⟨C₁ + C₂ + 1, by linarith, fun t => ?_⟩
  have hXlog := log_two_le_envelope t
  have hX0 : 0 < (1 + ‖t‖) * Real.log (2 + ‖t‖) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hXlog
  have h2exp : (2 : ℝ) ≤ Real.exp ((1 + ‖t‖) * Real.log (2 + ‖t‖)) := by
    have hle := Real.exp_le_exp.mpr hXlog
    rwa [Real.exp_log (by norm_num)] at hle
  have hmono₁ : C₁ * (1 + ‖t‖) * Real.log (2 + ‖t‖) ≤
      (C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖) := by nlinarith
  have hmono₂ : C₂ * (1 + ‖t‖) * Real.log (2 + ‖t‖) ≤
      (C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖) := by nlinarith
  have hexp : Real.exp ((C₁ + C₂ + 1) * (1 + ‖t‖) * Real.log (2 + ‖t‖)) =
      Real.exp ((1 + ‖t‖) * Real.log (2 + ‖t‖)) *
        Real.exp ((C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖xiPerturbed R t‖ ≤ ‖XiC t‖ + ‖(Polynomial.aeval (t ^ (2 : ℕ)) R : ℂ)‖ := norm_add_le _ _
    _ ≤ Real.exp (C₁ * (1 + ‖t‖) * Real.log (2 + ‖t‖)) +
          Real.exp (C₂ * (1 + ‖t‖) * Real.log (2 + ‖t‖)) := add_le_add (h₁ t) (h₂ t)
    _ ≤ Real.exp ((C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖)) +
          Real.exp ((C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖)) :=
        add_le_add (Real.exp_le_exp.mpr hmono₁) (Real.exp_le_exp.mpr hmono₂)
    _ ≤ Real.exp ((C₁ + C₂ + 1) * (1 + ‖t‖) * Real.log (2 + ‖t‖)) := by
        rw [hexp]
        nlinarith [Real.exp_pos ((C₁ + C₂) * (1 + ‖t‖) * Real.log (2 + ‖t‖))]

/-- The seam-jet clause: divisibility by `X ^ (N+1)` makes the perturbation vanish to order
`2N+2` at the seam. -/
theorem xiPerturbed_seamJet {R : Polynomial ℝ} {N : ℕ}
    (hdvd : (X : Polynomial ℝ) ^ (N + 1) ∣ R) :
    ∃ S : Polynomial ℝ, ∀ t : ℂ,
      xiPerturbed R t - XiC t = t ^ (2 * N + 2) * (Polynomial.aeval (t ^ (2 : ℕ)) S : ℂ) := by
  obtain ⟨S, hS⟩ := hdvd
  refine ⟨S, fun t => ?_⟩
  have hexp : 2 * (N + 1) = 2 * N + 2 := by omega
  rw [xiPerturbed_sub_XiC, hS, map_mul, map_pow, Polynomial.aeval_X, ← pow_mul, hexp]

/-! ### The master construction -/

/-- **Finite-codimension constraint data cannot select RH.**  For every real subspace of finite
codimension in the polynomial perturbation sector and every seam-jet order, there is a
perturbation inside that subspace, vanishing to the prescribed order at the seam, whose perturbed
completed function is even, Schwarz-real, carries the same order-one envelope, and has a non-real
zero quartet. -/
theorem exists_offLine_perturbation (W : Submodule ℝ (Polynomial ℝ))
    [FiniteDimensional ℝ ((Polynomial ℝ) ⧸ W)] {m : ℕ}
    (hW : Module.finrank ℝ ((Polynomial ℝ) ⧸ W) ≤ m) (N : ℕ) :
    ∃ (R : Polynomial ℝ) (τ : ℂ),
      R ∈ W ∧ ((X : Polynomial ℝ) ^ (N + 1) ∣ R) ∧ τ.im ≠ 0 ∧ (τ ^ (2 : ℕ)).im ≠ 0 ∧
        xiPerturbed R τ = 0 ∧ xiPerturbed R (-τ) = 0 ∧
        xiPerturbed R ((starRingEnd ℂ) τ) = 0 ∧
        xiPerturbed R (-((starRingEnd ℂ) τ)) = 0 := by
  obtain ⟨P, Q, hPW, hQW, hPdvd, hQdvd, hPQ⟩ := exists_indep_pair_of_finiteCodim W hW N
  obtain ⟨u, hu, hspan⟩ := exists_nonreal_spanning hPQ
  obtain ⟨τ, hτ⟩ : ∃ τ : ℂ, τ ^ (2 : ℕ) = u := IsAlgClosed.exists_pow_nat_eq u (by norm_num)
  have hτim : τ.im ≠ 0 := by
    intro h0
    refine hu ?_
    rw [← hτ, pow_two, Complex.mul_im, h0]
    ring
  obtain ⟨a, b, hab⟩ := hspan (-(XiC τ))
  refine ⟨a • P + b • Q, τ, W.add_mem (W.smul_mem a hPW) (W.smul_mem b hQW), ?_, hτim, ?_, ?_,
    ?_, ?_, ?_⟩
  · refine dvd_add ?_ ?_
    · rw [Polynomial.smul_eq_C_mul]
      exact hPdvd.mul_left _
    · rw [Polynomial.smul_eq_C_mul]
      exact hQdvd.mul_left _
  · rw [hτ]; exact hu
  · have hval : (Polynomial.aeval (τ ^ (2 : ℕ)) (a • P + b • Q) : ℂ) = -(XiC τ) := by
      rw [hτ, map_add, map_smul, map_smul]
      simpa [Algebra.smul_def] using hab
    rw [xiPerturbed, hval]
    ring
  · rw [xiPerturbed_even]
    have hval : (Polynomial.aeval (τ ^ (2 : ℕ)) (a • P + b • Q) : ℂ) = -(XiC τ) := by
      rw [hτ, map_add, map_smul, map_smul]
      simpa [Algebra.smul_def] using hab
    rw [xiPerturbed, hval]
    ring
  · rw [xiPerturbed_conj]
    have hval : (Polynomial.aeval (τ ^ (2 : ℕ)) (a • P + b • Q) : ℂ) = -(XiC τ) := by
      rw [hτ, map_add, map_smul, map_smul]
      simpa [Algebra.smul_def] using hab
    rw [xiPerturbed, hval]
    simp
  · rw [xiPerturbed_even, xiPerturbed_conj]
    have hval : (Polynomial.aeval (τ ^ (2 : ℕ)) (a • P + b • Q) : ℂ) = -(XiC τ) := by
      rw [hτ, map_add, map_smul, map_smul]
      simpa [Algebra.smul_def] using hab
    rw [xiPerturbed, hval]
    simp

/-- **Finite real-linear probes cannot select RH.** -/
theorem exists_offLine_perturbation_of_probes {m : ℕ}
    (L : Fin m → (Polynomial ℝ →ₗ[ℝ] ℝ)) (N : ℕ) :
    ∃ (R : Polynomial ℝ) (τ : ℂ),
      (∀ j, L j R = 0) ∧ ((X : Polynomial ℝ) ^ (N + 1) ∣ R) ∧ τ.im ≠ 0 ∧ (τ ^ (2 : ℕ)).im ≠ 0 ∧
        xiPerturbed R τ = 0 ∧ xiPerturbed R (-τ) = 0 ∧
        xiPerturbed R ((starRingEnd ℂ) τ) = 0 ∧
        xiPerturbed R (-((starRingEnd ℂ) τ)) = 0 := by
  classical
  set Λ : Polynomial ℝ →ₗ[ℝ] (Fin m → ℝ) := LinearMap.pi L with hΛ
  have hequiv := Λ.quotKerEquivRange
  haveI : FiniteDimensional ℝ ((Polynomial ℝ) ⧸ LinearMap.ker Λ) :=
    hequiv.symm.finiteDimensional
  have hrank : Module.finrank ℝ ((Polynomial ℝ) ⧸ LinearMap.ker Λ) ≤ m := by
    rw [hequiv.finrank_eq]
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  obtain ⟨R, τ, hRW, hdvd, hτ1, hτ2, hz1, hz2, hz3, hz4⟩ :=
    exists_offLine_perturbation (LinearMap.ker Λ) hrank N
  refine ⟨R, τ, fun j => ?_, hdvd, hτ1, hτ2, hz1, hz2, hz3, hz4⟩
  have hker : Λ R = 0 := hRW
  have := congrFun hker j
  simpa [hΛ, LinearMap.pi_apply] using this

/-- **Finite-codimension landscape slices cannot select RH.** -/
theorem exists_offLine_perturbation_of_finiteCodim (U : Submodule ℝ (Polynomial ℝ))
    [FiniteDimensional ℝ ((Polynomial ℝ) ⧸ U)] (N : ℕ) :
    ∃ (R : Polynomial ℝ) (τ : ℂ),
      R ∈ U ∧ ((X : Polynomial ℝ) ^ (N + 1) ∣ R) ∧ τ.im ≠ 0 ∧ (τ ^ (2 : ℕ)).im ≠ 0 ∧
        xiPerturbed R τ = 0 ∧ xiPerturbed R (-τ) = 0 ∧
        xiPerturbed R ((starRingEnd ℂ) τ) = 0 ∧
        xiPerturbed R (-((starRingEnd ℂ) τ)) = 0 :=
  exists_offLine_perturbation U (le_refl (Module.finrank ℝ ((Polynomial ℝ) ⧸ U))) N

/-- **A prescribed non-real quartet is reachable at every seam-jet order.** -/
theorem exists_offLine_perturbation_prescribed {τ : ℂ} (hτ : (τ ^ (2 : ℕ)).im ≠ 0) (N : ℕ) :
    ∃ R : Polynomial ℝ, ((X : Polynomial ℝ) ^ (N + 1) ∣ R) ∧
      xiPerturbed R τ = 0 ∧ xiPerturbed R (-τ) = 0 ∧
      xiPerturbed R ((starRingEnd ℂ) τ) = 0 ∧
      xiPerturbed R (-((starRingEnd ℂ) τ)) = 0 := by
  set u : ℂ := τ ^ (2 : ℕ) with hu
  have hune : u ≠ 0 := by
    intro h0
    rw [h0] at hτ
    simp at hτ
  have hcross : (u ^ (N + 1)).re * (u ^ (N + 2)).im -
      (u ^ (N + 1)).im * (u ^ (N + 2)).re ≠ 0 := by
    have hid : (starRingEnd ℂ) (u ^ (N + 1)) * u ^ (N + 2) =
        ((Complex.normSq u ^ (N + 1) : ℝ) : ℂ) * u := by
      rw [map_pow, show u ^ (N + 2) = u ^ (N + 1) * u from by ring, ← mul_assoc,
        ← mul_pow, mul_comm ((starRingEnd ℂ) u) u, Complex.mul_conj]
      push_cast
      ring
    have him : ((starRingEnd ℂ) (u ^ (N + 1)) * u ^ (N + 2)).im =
        (u ^ (N + 1)).re * (u ^ (N + 2)).im - (u ^ (N + 1)).im * (u ^ (N + 2)).re := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [← him, hid]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have hns : Complex.normSq u ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using hune
    exact mul_ne_zero (pow_ne_zero _ hns) hτ
  obtain ⟨a, b, hab⟩ := exists_real_combination (w := -(XiC τ)) hcross
  set R : Polynomial ℝ := a • X ^ (N + 1) + b • X ^ (N + 2) with hR
  have hval : (Polynomial.aeval (τ ^ (2 : ℕ)) R : ℂ) = -(XiC τ) := by
    rw [hR, map_add, map_smul, map_smul, map_pow, map_pow, Polynomial.aeval_X, ← hu]
    simpa [Algebra.smul_def] using hab
  have hzero : xiPerturbed R τ = 0 := by
    rw [xiPerturbed, hval]
    ring
  refine ⟨R, ?_, hzero, ?_, ?_, ?_⟩
  · rw [hR]
    refine dvd_add ?_ ?_
    · rw [Polynomial.smul_eq_C_mul]
      exact (dvd_refl ((X : Polynomial ℝ) ^ (N + 1))).mul_left _
    · rw [Polynomial.smul_eq_C_mul]
      exact (pow_dvd_pow (X : Polynomial ℝ) (by omega : N + 1 ≤ N + 2)).mul_left _
  · rw [xiPerturbed_even]
    exact hzero
  · rw [xiPerturbed_conj, hzero, map_zero]
  · rw [xiPerturbed_even, xiPerturbed_conj, hzero, map_zero]

/-- **Finite-type source functors cannot select RH.**  If the output of a source functor on the
even polynomial-tail sector factors through finitely many real-linear observables of the
perturbation, then it takes the same value on a perturbed function with a non-real zero quartet as
it does on the unperturbed one. -/
theorem exists_offLine_perturbation_of_finiteType {m : ℕ} {β : Type*}
    (L : Fin m → (Polynomial ℝ →ₗ[ℝ] ℝ)) (G : (Fin m → ℝ) → β) (N : ℕ) :
    ∃ (R : Polynomial ℝ) (τ : ℂ),
      G (fun j => L j R) = G (fun j => L j 0) ∧
        ((X : Polynomial ℝ) ^ (N + 1) ∣ R) ∧ τ.im ≠ 0 ∧ (τ ^ (2 : ℕ)).im ≠ 0 ∧
        xiPerturbed R τ = 0 ∧ xiPerturbed R (-τ) = 0 ∧
        xiPerturbed R ((starRingEnd ℂ) τ) = 0 ∧
        xiPerturbed R (-((starRingEnd ℂ) τ)) = 0 := by
  obtain ⟨R, τ, hL, hdvd, hτ1, hτ2, hz1, hz2, hz3, hz4⟩ :=
    exists_offLine_perturbation_of_probes L N
  refine ⟨R, τ, ?_, hdvd, hτ1, hτ2, hz1, hz2, hz3, hz4⟩
  congr 1
  funext j
  rw [hL j, map_zero]

end RHTower
