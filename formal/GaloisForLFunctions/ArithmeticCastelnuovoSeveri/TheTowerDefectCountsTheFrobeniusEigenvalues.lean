import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryPrimeSeesEveryRightZero
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface

/-!
# The tower defect counts the Frobenius eigenvalues

The tower Pontryagin law (`tower_pontryagin_law`) counts the outer Frobenius eigenvalues
`b = p^{ρ − ½}` whose weight `W_b = Σ_{β(τ) = b} X_τ(g) conj X_{1−τ̄}(g)` does not vanish. Zeros that
share an eigenvalue — at a resonant prime — could cancel each other's weight. This file removes the
weights from the law: for a configuration with finitely many right zeros there is one test whose
tower at **every** prime `p` has defect exactly `#{p^{ρ − ½} : Re ρ > ½}`, the number of distinct
outer Frobenius eigenvalues (`exists_test_tower_defect_eq_card_frobEig`).

For the modulated bump `g_s = φ e^{isu}` the cross-correlation is `e^{isu} A(u)`, `A = φ ⋆ φ̃`
(`weilTest_mul_cexp`), so the weight of a class is the transform at the real point `s` of

    G_b(u) = A(u) Σ_{β(τ) = b} m_τ e^{iγ_τ u}       (`classKernel`, `frobWeight_probe`),

a compactly supported function with `G_b(0) = A(0) Σ m_τ ≠ 0`. By Fourier injectivity
(`eq_zero_of_paperFT_real_eq_zero`) its transform is a nonzero entire function of `s`, so the bad
frequencies of each class are countable; there are countably many primes and finitely many classes
at each, so some `s` makes every weight at every prime nonzero.

Together with `subsingleton_resonantPrimes`: one prime tower of one test sees exactly the distinct
eigenvalues `p^{ρ − ½}`, which are all the right zeros except at finitely many resonant primes.
-/

open Complex MeasureTheory
open scoped ComplexConjugate Classical FourierTransform
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Modulation by a complex frequency shifts the transform: `h_{K e^{iwu}}(z) = h_K(z + w)`. -/
theorem paperFT_mul_cexp (K : ℝ → ℂ) (w z : ℂ) :
    paperFT (fun u => K u * cexp (I * w * u)) z = paperFT K (z + w) := by
  simp only [paperFT]
  congr 1
  funext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **Fourier injectivity.** A continuous compactly supported function whose transform vanishes on
the real line is zero. -/
theorem eq_zero_of_paperFT_real_eq_zero {G : ℝ → ℂ} (hG : Continuous G)
    (hGc : HasCompactSupport G) (h : ∀ s : ℝ, paperFT G s = 0) (u : ℝ) : G u = 0 := by
  have hF : 𝓕 G = 0 := by
    funext v
    have hv := h (-2 * Real.pi * v)
    rw [EF.paperFT_ofReal_eq_fourier,
      show -(-2 * Real.pi * v) / (2 * Real.pi) = v by field_simp] at hv
    rw [Pi.zero_apply, hv]
  rw [EF.paper_inversion hG (hG.integrable_of_hasCompactSupport hGc)
    (by rw [hF]; exact integrable_zero _ _ _) u]
  simp [h]

/-- The transform of a finite sum of compactly supported continuous functions. -/
theorem paperFT_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ S, Continuous (F i)) (hFc : ∀ i ∈ S, HasCompactSupport (F i)) (z : ℂ) :
    paperFT (fun u => ∑ i ∈ S, F i u) z = ∑ i ∈ S, paperFT (F i) z := by
  simp only [paperFT, Finset.sum_mul]
  exact integral_finsetSum S fun i hi =>
    ((hF i hi).mul (by fun_prop)).integrable_of_hasCompactSupport (hFc i hi).mul_right

/-- The cross-correlation of a modulated test is the modulated cross-correlation. -/
theorem weilTest_mul_cexp (φ : ℝ → ℂ) (s u : ℝ) :
    EF.weilTest (fun t => φ t * cexp (I * s * t)) (fun t => φ t * cexp (I * s * t)) u =
      cexp (I * s * u) * EF.weilTest φ φ u := by
  rw [RHTower.weilTest_apply, RHTower.weilTest_apply, ← integral_const_mul]
  congr 1
  funext t
  rw [map_mul, ← Complex.exp_conj]
  have hc : conj (I * (s : ℂ) * ((t - u : ℝ) : ℂ)) = -(I * s * ((t - u : ℝ) : ℂ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hc]
  have he : cexp (I * s * t) * cexp (-(I * s * ((t - u : ℝ) : ℂ))) = cexp (I * s * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (φ t * conj (φ (t - u))) * he

/-- The short bump of the probes. -/
abbrev bump0 : ℝ → ℂ := bumpTest (1 / 2) (by norm_num) 0

/-- Its autocorrelation `A = φ ⋆ φ̃`. -/
def bumpAuto : ℝ → ℂ := EF.weilTest bump0 bump0

theorem bumpAuto_contDiff : ContDiff ℝ 2 bumpAuto :=
  EF.weilTest_contDiff (bumpTest_contDiff _ 0) (bumpTest_contDiff _ 0).continuous
    (bumpTest_hasCompactSupport _ 0)

theorem bumpAuto_hasCompactSupport : HasCompactSupport bumpAuto :=
  EF.weilTest_hasCompactSupport (bumpTest_hasCompactSupport _ 0) (bumpTest_hasCompactSupport _ 0)

/-- `A(0) = ∫ φ² ≠ 0`. -/
theorem bumpAuto_zero_ne_zero : bumpAuto 0 ≠ 0 := by
  set ψ := smallBump (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have h0 : ψ 0 = 1 := ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)
  have hpos : 0 < ∫ t, ψ t * ψ t :=
    (ψ.continuous.mul ψ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      ψ.hasCompactSupport.mul_left (fun t => mul_self_nonneg (ψ t))
      (show (fun t => ψ t * ψ t) 0 ≠ 0 by simp [h0])
  have he : bumpAuto 0 = ((∫ t, ψ t * ψ t : ℝ) : ℂ) := by
    rw [bumpAuto, RHTower.weilTest_apply, ← integral_complex_ofReal]
    congr 1
    funext t
    simp [bumpTest, ψ, Complex.conj_ofReal]
  rw [he]
  exact_mod_cast hpos.ne'

/-! ### Class kernels -/

/-- The right zeros as carrier points. -/
def rightCarrierSet (Z : ZeroConfig) : Set Z.carrier := {τ | 1 / 2 < (τ : ℂ).re}

theorem rightCarrierSet_finite (Z : ZeroConfig) (hR : (rightZeros Z).Finite) :
    (rightCarrierSet Z).Finite :=
  (hR.preimage Subtype.val_injective.injOn).subset fun τ hτ => ⟨τ.2, hτ⟩

/-- The right zeros with Frobenius eigenvalue `b` at scale `ℓ`. -/
def outerClass (Z : ZeroConfig) (hR : (rightZeros Z).Finite) (ℓ : ℝ) (b : ℂ) :
    Finset Z.carrier :=
  (rightCarrierSet_finite Z hR).toFinset.filter fun τ => frobEig ℓ τ = b

/-- The class kernel `G_b(u) = A(u) Σ_{β(τ) = b} m_τ e^{iγ_τ u}`. -/
def classKernel (Z : ZeroConfig) (hR : (rightZeros Z).Finite) (ℓ : ℝ) (b : ℂ) (u : ℝ) : ℂ :=
  bumpAuto u * ∑ τ ∈ outerClass Z hR ℓ b, (Z.mult τ : ℂ) * cexp (I * gammaOf τ * u)

theorem classKernel_continuous (Z : ZeroConfig) (hR : (rightZeros Z).Finite) (ℓ : ℝ) (b : ℂ) :
    Continuous (classKernel Z hR ℓ b) :=
  bumpAuto_contDiff.continuous.mul (continuous_finsetSum _ fun τ _ => by fun_prop)

theorem classKernel_hasCompactSupport (Z : ZeroConfig) (hR : (rightZeros Z).Finite) (ℓ : ℝ)
    (b : ℂ) : HasCompactSupport (classKernel Z hR ℓ b) :=
  bumpAuto_hasCompactSupport.mul_right

/-- An outer class is nonempty, so `G_b(0) = A(0) Σ m_τ ≠ 0`. -/
theorem classKernel_zero_ne_zero (Z : ZeroConfig) (hR : (rightZeros Z).Finite) {ℓ : ℝ}
    {b : ℂ} (hb : b ∈ outerEig Z ℓ) : classKernel Z hR ℓ b 0 ≠ 0 := by
  obtain ⟨ρ, hρ, rfl⟩ := hb
  have hmem : (⟨ρ, hρ.1⟩ : Z.carrier) ∈ outerClass Z hR ℓ (frobEig ℓ ρ) :=
    Finset.mem_filter.mpr ⟨(rightCarrierSet_finite Z hR).mem_toFinset.mpr hρ.2, rfl⟩
  have hsum : 0 < ∑ τ ∈ outerClass Z hR ℓ (frobEig ℓ ρ), Z.mult τ :=
    Finset.sum_pos' (fun τ _ => Nat.zero_le _) ⟨_, hmem, Z.one_le_mult _ hρ.1⟩
  simp only [classKernel, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  refine mul_ne_zero bumpAuto_zero_ne_zero ?_
  rw [← Nat.cast_sum]
  exact_mod_cast hsum.ne'

/-- The transform of a class kernel vanishes at countably many real frequencies. -/
theorem countable_badFreq (Z : ZeroConfig) (hR : (rightZeros Z).Finite) {ℓ : ℝ} {b : ℂ}
    (hb : b ∈ outerEig Z ℓ) : {s : ℝ | paperFT (classKernel Z hR ℓ b) s = 0}.Countable := by
  have hG := classKernel_continuous Z hR ℓ b
  have hGc := classKernel_hasCompactSupport Z hR ℓ b
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℝ, paperFT (classKernel Z hR ℓ b) s ≠ 0 := by
    by_contra h
    push Not at h
    exact classKernel_zero_ne_zero Z hR hb (eq_zero_of_paperFT_real_eq_zero hG hGc h 0)
  exact (countable_zeros_of_entire_nonzero
    (RHTower.EvenSector.differentiable_paperFT_of_compact hG hGc) hs₀).preimage
      Complex.ofReal_injective

/-! ### Weights of modulated bumps -/

/-- The weight term of a probe: `X_τ(g_s) conj X_{1−τ̄}(g_s) = m_τ · h_{A e^{iγ_τ ·}}(s)`. -/
theorem zeroCoord_mul_conj_reflect_probe (Z : ZeroConfig) (s : ℝ) (τ : Z.carrier) :
    zeroCoord Z (probe s 0) τ * conj (zeroCoord Z (probe s 0) (reflectCarrier Z τ)) =
      (Z.mult τ : ℂ) * paperFT (fun u => bumpAuto u * cexp (I * gammaOf τ * u)) s := by
  have hm : Z.mult (reflect (τ : ℂ)) = Z.mult τ := Z.mult_reflect _ τ.2
  have hsq : ((Real.sqrt (Z.mult τ) : ℝ) : ℂ) * (Real.sqrt (Z.mult τ) : ℝ) = (Z.mult τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hprobe : probe s 0 = fun t => bump0 t * cexp (I * s * t) := rfl
  have hfun : EF.weilTest (probe s 0) (probe s 0) =
      fun u => bumpAuto u * cexp (I * (s : ℂ) * u) := by
    funext u
    rw [hprobe, weilTest_mul_cexp, bumpAuto, mul_comm]
  have hW : paperFT (probe s 0) (gammaOf τ) * conj (paperFT (probe s 0) (conj (gammaOf τ))) =
      paperFT (fun u => bumpAuto u * cexp (I * gammaOf τ * u)) s := by
    rw [← EF.paperFT_weilTest (probe_contDiff s 0).continuous (probe_contDiff s 0).continuous
      (probe_hasCompactSupport s 0) (probe_hasCompactSupport s 0), hfun, paperFT_mul_cexp,
      paperFT_mul_cexp, add_comm]
  simp only [zeroCoord, reflectCarrier, hm, gammaOf_reflect, map_mul, Complex.conj_ofReal]
  rw [← hW]
  linear_combination (paperFT (probe s 0) (gammaOf ↑τ) *
    conj (paperFT (probe s 0) (conj (gammaOf ↑τ)))) * hsq

/-- **The weight of an outer class is a transform**: `W_b(g_s) = h_{G_b}(s)`. -/
theorem frobWeight_probe (Z : ZeroConfig) (hR : (rightZeros Z).Finite) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℂ} (hb : b ∈ outerEig Z ℓ) (s : ℝ) :
    frobWeight Z (probe s 0) ℓ b = paperFT (classKernel Z hR ℓ b) s := by
  have hn := one_lt_norm_of_mem_outerEig hℓ hb
  have hsupp : ∀ τ ∉ outerClass Z hR ℓ b, (if frobEig ℓ τ = b then
      zeroCoord Z (probe s 0) τ * conj (zeroCoord Z (probe s 0) (reflectCarrier Z τ)) else 0) = 0 := by
    intro τ hτ
    rw [if_neg]
    intro he
    apply hτ
    refine Finset.mem_filter.mpr ⟨(rightCarrierSet_finite Z hR).mem_toFinset.mpr ?_, he⟩
    show 1 / 2 < (τ : ℂ).re
    exact (one_lt_norm_frobEig_iff hℓ _).mp (by rw [he]; exact hn)
  have hker : classKernel Z hR ℓ b = fun u => ∑ τ ∈ outerClass Z hR ℓ b,
      (Z.mult τ : ℂ) * (bumpAuto u * cexp (I * gammaOf τ * u)) := by
    funext u
    rw [classKernel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => by ring
  have hsum := paperFT_finset_sum (outerClass Z hR ℓ b)
    (fun τ u => (Z.mult τ : ℂ) * (bumpAuto u * cexp (I * gammaOf τ * u)))
    (fun τ _ => continuous_const.mul (bumpAuto_contDiff.continuous.mul (by fun_prop)))
    (fun τ _ => bumpAuto_hasCompactSupport.mul_right.mul_left) s
  rw [frobWeight, tsum_eq_sum hsupp, hker, hsum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [if_pos (Finset.mem_filter.mp hτ).2, zeroCoord_mul_conj_reflect_probe]
  simp only [paperFT, mul_assoc]
  rw [integral_const_mul]

/-! ### The exact tower law -/

/-- **The tower defect counts the Frobenius eigenvalues.** For a tempered configuration with finitely
many right zeros there is one test `g` such that at every prime `p` the Weil form has `n` negative
squares on some window of the tower `g(· − k log p)` iff there are at least `n` distinct outer
eigenvalues `p^{ρ − ½}`. -/
theorem exists_test_tower_defect_eq_card_frobEig (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g (Real.log p) K)) ↔
        (n : ℕ∞) ≤ (frobEig (Real.log p) '' rightZeros Z).encard := by
  set B : Set ℝ := ⋃ p ∈ {p : ℕ | p.Prime}, ⋃ b ∈ outerEig Z (Real.log p),
    {s : ℝ | paperFT (classKernel Z hR (Real.log p) b) s = 0} with hBdef
  have hB : B.Countable := by
    refine (Set.to_countable _).biUnion fun p _ => ?_
    exact (hR.image _).countable.biUnion fun b hb => countable_badFreq Z hR hb
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hB.mono fun s _ => h s)
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun p hp n => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hO : (outerEig Z (Real.log p)).Finite := hR.image _
  have hvis : visibleEig Z (probe s 0) (Real.log p) hO = hO.toFinset := by
    refine Finset.filter_true_of_mem fun b hb => ?_
    have hbO := hO.mem_toFinset.mp hb
    rw [frobWeight_probe Z hR hℓ hbO]
    intro h0
    exact hs (Set.mem_biUnion (show p ∈ {p : ℕ | p.Prime} from hp) (Set.mem_biUnion hbO h0))
  rw [tower_pontryagin_law Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0) hℓ hO n, hvis,
    show frobEig (Real.log p) '' rightZeros Z = outerEig Z (Real.log p) from rfl,
    hO.encard_eq_coe_toFinset_card, ENat.coe_le_coe]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
