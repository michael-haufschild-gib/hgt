import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.Family
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.CoefficientConvolution
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.RealCharacterConvolution
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.RayClassCountingBounds
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.QuadraticMangoldtBound
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.ImaginaryQuadraticField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.RayClassCardinality

/-! Integral ideals realize all coefficients and bounds of the quadratic ray class family. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

section

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

theorem aRay_norm_zero (g : D.G) : aRay D g 0 = 0 := by
  have : idealsIn D g 0 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h2, -⟩
    exact h1 (Ideal.absNorm_eq_zero_iff.1 h2)
  simp [aRay, this]

theorem aRay_one_norm_one : aRay D 1 1 = 1 := by
  have : idealsIn D 1 1 = {⊤} := by
    ext I
    simp only [idealsIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, h2, -⟩
      exact Ideal.absNorm_eq_one_iff.1 h2
    · rintro rfl
      refine ⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩
      rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  simp [aRay, this]

theorem aRay_norm_one_of_ne {g : D.G} (hg : g ≠ 1) : aRay D g 1 = 0 := by
  have : idealsIn D g 1 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, h2, h3⟩
    rw [Ideal.absNorm_eq_one_iff.1 h2, D.cls_top] at h3
    exact hg h3.symm
  simp [aRay, this]

end

theorem addChar_eq_one_or_neg_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    rw [← AddChar.mul_apply, h, AddChar.one_apply]
  exact mul_self_eq_one_iff.1 this

private theorem ray_parameter_bounds {d M : ℕ} (hd : 100 ≤ d) (hM : 3 ≤ M) :
    4 ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 ∧
      1 / (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤
        2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) ∧
      2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) ≤ 4 := by
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith only [hMR]
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith only [hdR])
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hsd : Real.sqrt d ≤ d := by
    calc
      Real.sqrt d = 1 * Real.sqrt d := (one_mul _).symm
      _ ≤ Real.sqrt d * Real.sqrt d :=
        mul_le_mul_of_nonneg_right (by linarith only [hs]) (Real.sqrt_nonneg _)
      _ = d := hss
  have hm : (100 : ℝ) * 9 ≤ (d : ℝ) * (M : ℝ) ^ 2 :=
    mul_le_mul hdR hM2 (by norm_num) (Nat.cast_nonneg _)
  have hm₀ : 0 < (M : ℝ) ^ 2 := by linarith only [hM2]
  have hs₀ : 0 < Real.sqrt d := by linarith only [hs]
  have hd₀ : 0 < (d : ℝ) := by linarith only [hdR]
  refine ⟨by linarith only [hm], ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc
      Real.sqrt d * (M : ℝ) ^ 2 ≤ (d : ℝ) * (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsd hm₀.le
      _ ≤ (8 * Real.pi) * ((d : ℝ) * (M : ℝ) ^ 2) := by
        have h : 1 ≤ 8 * Real.pi := by linarith only [Real.two_le_pi]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h (mul_nonneg hd₀.le hm₀.le)
      _ = _ := by ring
  · rw [div_le_iff₀ (by positivity)]
    have hden : (10 : ℝ) * 9 ≤ Real.sqrt d * (M : ℝ) ^ 2 :=
      mul_le_mul hs hM2 (by norm_num) hs₀.le
    linarith only [hden, Real.pi_le_four]

private theorem ray_sq_additive {K : Type} [Field K] [NumberField K] {M : ℕ}
    (D : RayData K M) (hM : 2 ≤ M) (χ : AddChar (Additive D.G) ℂ) (hχ : χ * χ = 1) (n : ℕ) :
    letI : Fintype (Additive D.G) := D.fin
    0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g : Additive D.G, aRay D g.toMul p.1) *
      ∑ g : Additive D.G, (χ g).re * aRay D g.toMul p.2 ∧
    ∑ g : Additive D.G, aRay D g.toMul n ≤
      ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g : Additive D.G, aRay D g.toMul p.1) *
        ∑ g : Additive D.G, (χ g).re * aRay D g.toMul p.2 := by
  letI : Fintype (Additive D.G) := D.fin
  let ε (g : D.G) := (χ (Additive.ofMul g)).re
  have he : ε 1 = 1 := by simp [ε]
  have hm (g h : D.G) : ε (g * h) = ε g * ε h := by
    change (χ (Additive.ofMul (g * h))).re = (χ (Additive.ofMul g)).re * (χ (Additive.ofMul h)).re
    rw [ofMul_mul, AddChar.map_add_eq_mul]
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]
  have hp (g : D.G) : ε g = 1 ∨ ε g = -1 := by
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [ε, h1]
  exact RaySq.conv_real_char K M hM D ε he hm hp n

private noncomputable def rayCoefficientFamily {K : Type} [Field K] [NumberField K] {M : ℕ}
    (D : RayData K M) (hM : 2 ≤ M) (B κ : ℝ) (hB : 4 ≤ B)
    (hcard : (Fintype.card D.G : ℝ) ≤ B) (hκ_ge : 1 / B ≤ κ) (hκ_le : κ ≤ 4)
    (hcount : ∀ (g : D.G) (x : ℝ), 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, aRay D g n - κ * x| ≤ 10 * Real.sqrt x)
    (htheta : ∀ (g : D.G) (t : ℝ), 0 < t → t ≤ 1 →
      |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) - κ / t| ≤ B ^ 10 * t)
    (hlam : ∀ g n, 0 ≤ lamRay D g n)
    (hlam_le : ∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) : LFam where
  G := Additive D.G
  ag := Additive.addCommGroup
  ft := D.fin
  B := B
  κ := κ
  a := fun g n => aRay D g.toMul n
  lam := fun g n => lamRay D g.toMul n
  B_ge := hB
  card_le := hcard
  κ_ge := hκ_ge
  κ_le := hκ_le
  a_nonneg := fun _ _ => Nat.cast_nonneg _
  a_zero := fun g => aRay_norm_zero D g.toMul
  a_one := (congrArg (fun g : D.G => aRay D g 1) (toMul_zero (α := D.G))).trans
    (aRay_one_norm_one D)
  a_one_ne := fun g hg => aRay_norm_one_of_ne D (g := g.toMul) (fun h => hg (by
    simpa only [ofMul_toMul, ofMul_one] using congrArg (@Additive.ofMul D.G) h))
  count := fun g => hcount g.toMul
  theta := fun g => htheta g.toMul
  lam_nonneg := fun g => hlam g.toMul
  lam_le := hlam_le
  conv := fun g n => RayConv.aRay_mul_log K M hM D g.toMul n
  sq := ray_sq_additive D hM

theorem exists_lFam_ray : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M →
    ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧
      ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro d M hd hd4 hd100 hM
  obtain ⟨K, _, _, ω, -, hK, hdisc, hω, hgen, hnorm⟩ :=
    GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4
  have hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K) := by
    have h := congrArg (algebraMap (𝓞 K) K) hω
    simpa using h
  let D : RayData K M := rayData K M (by omega)
  have hc := rayCountTheta K d M _ hd hd4 hd100 hx hK hM D
  have hl := LamRay.lamRay_props D hK ω hgen hnorm
  have hcard := rayClass_card_le D hK
  rw [hdisc, Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)] at hcard
  obtain ⟨hB, hκ_ge, hκ_le⟩ := ray_parameter_bounds hd100 hM
  have hcard' : (Fintype.card D.G : ℝ) ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 := by
    exact hcard.trans (by linarith only [show 0 ≤ (d : ℝ) * (M : ℝ) ^ 2 by positivity])
  let 𝓕 := rayCoefficientFamily D (by omega) _ _ hB hcard' hκ_ge hκ_le
    (fun g => (hc g).1) (fun g => (hc g).2) hl.1 hl.2.1
  refine ⟨𝓕, rfl, fun p hp h => ?_⟩
  change lamRay D (0 : Additive D.G).toMul p ≠ 0 at h
  rw [toMul_zero] at h
  exact hl.2.2 p hp h

end GlobalTheory.Hk
