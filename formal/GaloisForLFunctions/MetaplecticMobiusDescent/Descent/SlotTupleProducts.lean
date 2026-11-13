/-
Slot tuple products adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.HeathBrownIteration
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.HybridRows

/-!
# Slot tuple products

Slot tuple products and slot product coefficients; label and row exponents, puncture widths and
row radii of actual cells, with correlated source gates.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

theorem hybrid_original_quotient_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L A H : ℝ,
      1 ≤ K → 1 ≤ X → 1 ≤ N → 1 ≤ A → 1 ≤ H →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (cset : Ideal Eis → Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (p.1 * p.2)) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, hblock⟩ := hybrid_fixed_block_sieve_norm ε hε
  refine ⟨C * (128 * 128 * 256), by positivity, ?_⟩
  intro K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ 0 := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ 0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hP0 : ∀ P ∈ Pset, P ≠ 0 := fun P hP' => (hP P hP').1.1.ne_zero
  have hHcount : (Hset.card : ℝ) ≤ 128 * H := by
    apply EisensteinLatticeCount.finite_ideal_count_real Hset H hH
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).1
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ 128 * A := by
    intro p hp
    exact EisensteinLatticeCount.finite_ideal_count_real (cset p.1) A hA
      (fun c hc => (hcs p hp c hc).1) (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock K X N (2 * L) hK hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_quadratic_admissible (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows K
        (fun k hk => (hrows k hk).1.1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient R r h t a)
    (hybridColumnCoefficient R r beta) (128 * A) 256 (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_cubic_admissible r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_cubic_admissible R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy R r h t hR Pset L hP0
      (fun P hP' => (hP P hP').2) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (K * X * N) ^ ε * (K + X) * (128 * A) * (128 * H) *
        CubicSieve.sieveNorm N (2 * L) * 256) := by
      gcongr
      exact sq_nonneg _
    _ = _ := by ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

theorem hybrid_extracted_dyadic_block_nonempty (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (quotientGridSupport r (hybridGridSupport D)).Nonempty →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_original_quotient_block ε hε
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta hQ
  let Q := quotientGridSupport r (hybridGridSupport D)
  let X := N * B / (C ^ 2 * T ^ 2)
  let A := 2 * C / (Ideal.absNorm r : ℝ)
  let H := B / (C * T ^ 2)
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have hnr : 0 < (Ideal.absNorm r : ℝ) := descentIdealNorm_pos hr
  have hnorm (d : HybridColumnData) (hd : d ∈ D) :
      (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
      (Ideal.absNorm d.residualB : ℝ) ≤ H ∧
      (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ X := by
    have hd' := hD d hd
    apply d.residual_norm_bounds N B C T (by linarith) (by linarith) hC0 hT0
      (hn _ hd'.2.2.2.1).2 hd'.2.2.2.2 hd'.2.1
    simpa only [hd'.1] using ht
  have hcBound (d : HybridColumnData) (hd : d ∈ D) (c : Ideal Eis)
      (hdc : d.common = r * c) : c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A := by
    have hcz : c ≠ 0 := by
      intro hz
      apply d.common_ne_zero
      simp [hdc, hz]
    refine ⟨hcz, (le_div_iff₀ hnr).mpr ?_⟩
    have hdcN := (hD d hd).2.2.1
    rw [hdc, map_mul, Nat.cast_mul] at hdcN
    simpa only [mul_comm] using hdcN
  have hpair (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst) :
      Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X ∧
      p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H := by
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, he, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 hu
    have he' : (d.residualN, d.residualB) = p := he.trans hup
    have hm := congrArg Prod.fst he'
    have hh := congrArg Prod.snd he'
    have hdB : d.residualB ≠ 0 :=
      ne_zero_of_dvd_ne_zero d.g_squarefree.ne_zero (dvd_mul_left _ _)
    exact ⟨by simpa only [← hm, ← hh] using d.residual_product_squarefree,
      by simpa only [← hm, ← hh] using (hnorm d hd).2.2,
      by simpa only [← hh] using hdB,
      by simpa only [← hh] using (hnorm d hd).2.1⟩
  have hcset (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst)
      (c : Ideal Eis) (hc : c ∈ gridCommonSupport Q p.1) :
      c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset := by
    obtain ⟨d, hd, hm, hdc⟩ := quotientGridCommonSupport_origin r hr D p.1 c hc
    have hc' := hcBound d hd c hdc
    exact ⟨hc'.1, hc'.2, by simpa only [hdc, hm] using (hD d hd).2.2.2.1⟩
  obtain ⟨u₀, hu₀⟩ := hQ
  have hp₀ : u₀.1 ∈ Q.image Prod.fst := Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : u₀.2 ∈ gridCommonSupport Q u₀.1.1 :=
    Finset.mem_image.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, rfl⟩, rfl⟩
  have hX : 1 ≤ X :=
    (descentIdealNorm_one_le (hpair u₀.1 hp₀).1.ne_zero).trans (hpair u₀.1 hp₀).2.1
  have hH : 1 ≤ H :=
    (descentIdealNorm_one_le (hpair u₀.1 hp₀).2.2.1).trans (hpair u₀.1 hp₀).2.2.2
  have hA : 1 ≤ A :=
    (descentIdealNorm_one_le (hcset u₀.1 hp₀ u₀.2 hc₀).1).trans
      (hcset u₀.1 hp₀ u₀.2 hc₀).2.1
  have hbGrid : ∀ u ∈ hybridGridSupport D, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact hbeta d hd
  have he := hblock K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset
    (Q.image Prod.fst) (gridCommonSupport Q) a
    (extractedGridCoefficient (hybridGridSupport D) R t beta)
    hrows hn hP ha (fun p hp => ⟨(hpair p hp).1, (hpair p hp).2.1⟩)
    (fun p hp => (hpair p hp).2.2) hcset
    (fun p _ c _ => extractedGridCoefficient_norm_le_one _ R t beta hbGrid (r * c) p.1 p.2)
  have hrow (k : Ideal Eis) (hk : k ∈ quotientSupport (R * r) rows) :=
    gridDivisorHybridBlock_extract (hybridGridSupport D) Pset a beta t k R r hR hr
      (hrows _ ((mem_quotientSupport (R * r) k (mul_ne_zero hR hr) rows).mp hk)).1
      (fun P hP' => (hP P hP').1)
  have he' : (∑ k ∈ quotientSupport (R * r) rows,
      ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₁ * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
    calc
      _ = _ := Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
      _ ≤ _ := he
  have hXupper : X ≤ N * B := by
    apply div_le_self (by positivity : 0 ≤ N * B)
    have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact one_le_mul_of_one_le_of_one_le hC2 hT2
  apply he'.trans
  calc
    _ ≤ C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
      have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
      gcongr
    _ = _ := by
      dsimp only [A, H]
      field_simp

theorem hybrid_extracted_dyadic_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := hybrid_extracted_dyadic_block_nonempty ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  by_cases hQ : (quotientGridSupport r (hybridGridSupport D)).Nonempty
  · exact he K N B L C T hK hN hB hC hT R r t hR hr ht
      rows nset Pset D a beta hrows hn hP ha hD hbeta hQ
  · have hQ' := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp only [gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty _ _ _ _ _ _ _ _ hQ',
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    positivity

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve 
noncomputable section
local notation "Eis" => Eisenstein.O

def hybridDivisorPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis × Ideal Eis) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal Eis) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (descentIdealNorm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal Eis)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := descent_finite_inverse_norm_sum (hybridDivisorPool rows) K
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  norm_num only [show (2 : ℝ) * 128 = 256 by norm_num] at hsum
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss 
noncomputable section
local notation "Eis" => Eisenstein.O

theorem hybrid_fixed_square_grid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (t : Ideal Eis), T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ rows, ‖maskedGridHybridRow (hybridGridSupport D) Pset a beta t k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_extracted_dyadic_block ε hε
  obtain ⟨C₂, hC₂, hmask⟩ := maskedGridHybridRow_divisor_energy ε hε
  refine ⟨C₁ * C₂ * 256 ^ 2, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT t ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  have hr0 : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K :=
    fun k hk => ⟨(hrows k hk).1.1, (hrows k hk).2⟩
  let E := C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
    CubicSieve.sieveNorm N (2 * L)
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hTprim : ∀ u ∈ hybridGridSupport D, primaryIdealGenerator (u.2 * u.1.1) ≠ 0 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact (hn _ (hD d hd).2.2.2.1).1.2
  have hterm (v : Ideal Eis × Ideal Eis) (hv : v ∈ hybridDivisorPairPool rows) :
      (∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) := by
    have hp := Finset.mem_product.mp (hybridDivisorPairPool_subset rows hv)
    have hR := (hybridDivisorPool_bounds rows K hr0 v.1 hp.1).1
    have hr := (hybridDivisorPool_bounds rows K hr0 v.2 hp.2).1
    by_cases hcop : IsCoprime v.1 v.2
    · rw [double_divisor_row_reindex rows (fun k hk => (hr0 k hk).1) v.1 v.2 hcop]
      have he := hblock K N B L C T hK hN hB hC hT v.1 v.2 t hR hr ht
        rows nset Pset D a beta hrows hn hP ha hD hbeta
      convert he using 1
      dsimp only [E]
      field_simp
    · simp only [gridDivisorHybridBlock_zero_of_not_coprime _ _ _ _ _ _ _ _ hcop
          (fun P hPP => (hP P hPP).1.2) hTprim,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0), ite_self, Finset.sum_const_zero]
      exact mul_nonneg hE (by positivity)
  have he := hmask K hK rows (hybridGridSupport D) Pset a beta t hr0
  have hsum : (∑ v ∈ hybridDivisorPairPool rows,
      ∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ hybridDivisorPairPool rows,
          E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = E * ∑ v ∈ hybridDivisorPairPool rows,
          1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hybrid_divisor_pair_inverse_norm_sum rows K hr0) hE
  apply he.trans
  calc
    _ ≤ C₂ * K ^ ε * (E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [E]; ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

def sourceGridCoefficient (beta : Ideal Eis → Ideal Eis → ℂ)
    (t c m h : Ideal Eis) : ℂ := beta (c * m) ((c * h) * t ^ 2)

theorem reconstructed_fixed_square_grid
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d) =
      (if IsCoprime k t then 1 else 0) *
        maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k := by
  unfold maskedGridHybridRow hybridGridSupport
  rw [Finset.sum_image]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro P hP
    simp only [reconstructedHybridTerm, HybridColumnData.gridIndex,
      sourceGridCoefficient, hD d hd]
    ac_rfl
  · intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg

theorem reconstructed_fixed_square_energy_le
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (rows Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤
      ∑ k ∈ rows,
        ‖maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  rw [reconstructed_fixed_square_grid D t hD Pset a beta k]
  by_cases hkt : IsCoprime k t
  · simp only [hkt, ite_true, one_mul, le_refl]
  · simp only [hkt, ite_false, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem finite_double_row_energy {I J : Type*} [Fintype I] [Fintype J]
    (rows : Finset (Ideal Eis)) (F : I → J → Ideal Eis → ℂ) (E : ℝ) (_hE : 0 ≤ E)
    (hF : ∀ i j, (∑ k ∈ rows, ‖F i j k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i, ∑ j, F i j k‖ ^ 2) ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 * E := by
  have hk (k : Ideal Eis) :
      ‖∑ i, ∑ j, F i j k‖ ^ 2 ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
          ∑ i, ∑ j, ‖F i j k‖ ^ 2 := by
    simpa only [one_mul, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul] using
      bounded_coefficient_sum_sq (fun _ : I × J => 1) (fun u => F u.1 u.2 k) (by simp)
  calc
    _ ≤ ∑ k ∈ rows, ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ‖F i j k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hk k)
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ∑ k ∈ rows, ‖F i j k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) * ∑ _i : I, ∑ _j : J, E := by
      gcongr with i hi j hj
      exact hF i j
    _ = _ := by simp; ring

theorem supportedHybridRow_energy_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryIdealGenerator p.1 ≠ 0 ∧ primaryIdealGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 *
          (columnDyadicLength N + 1 : ℝ) ^ 2 * (columnDyadicLength B + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hfixed⟩ := hybrid_fixed_square_grid_energy ε hε
  refine ⟨256 ^ 2 * C₁, by positivity, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  let nset := S.image Prod.fst
  let E := C₁ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
    CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2
  let F (j : Fin (columnDyadicLength B + 1)) (i : Fin (columnDyadicLength N + 1))
      (k : Ideal Eis) : ℂ :=
    ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      ∑ d ∈ hybridCommonBlock S N i t, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnset : ∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨⟨(hS p hp).1, (hS p hp).2.1⟩, (hS p hp).2.2.2.1⟩
  have hBsup : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B := fun p hp => (hS p hp).2.2.2.2
  have hlen : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B :=
    fun p hp => (hS p hp).2.2.2
  have hlabel (j : Fin (columnDyadicLength B + 1))
      (i : Fin (columnDyadicLength N + 1)) :
      (∑ k ∈ rows, ‖F j i k‖ ^ 2) ≤ 256 ^ 2 * E := by
    let Td := divisorDyadicScale j.val
    have hTd : 0 < Td := by dsimp only [Td]; linarith [divisorDyadicScale_ge_one j.val]
    have htEnergy (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j) :
        (∑ k ∈ rows, ‖∑ d ∈ hybridCommonBlock S N i t,
          ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤ E / Td ^ 2 := by
      let D := hybridCommonBlock S N i t
      have hD (d : HybridColumnData) (hd : d ∈ D) :
          d.square = t ∧ divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) ∧
          (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val ∧
          d.common * d.residualN ∈ nset ∧
          (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B := by
        obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
        have hdorig := (mem_hybridColumnSupport S d).mp hdS
        have hb := hybridCommonBlock_bounds S N B (by linarith) (by linarith) hlen i j t ht d hd
        exact ⟨hdt, hb.1, hb.2.1, Finset.mem_image.mpr ⟨d.reconstruct, hdorig, rfl⟩,
          hBsup d.reconstruct hdorig⟩
      have hβ : ∀ d ∈ D, ‖sourceGridCoefficient beta t d.common d.residualN d.residualB‖ ≤ 1 := by
        intro d hd
        have hdo := (mem_hybridColumnSupport S d).mp (Finset.mem_filter.mp hd).1
        simpa only [sourceGridCoefficient, ← (hD d hd).1, HybridColumnData.reconstruct] using
          hbeta d.reconstruct hdo
      have hfix := hfixed K N B L (divisorDyadicScale i.val) Td hK hN hB
        (divisorDyadicScale_ge_one i.val) (divisorDyadicScale_ge_one j.val) t
        (divisorDyadicBin_bounds (hybridSquarePool S) B (hybridSquarePool_bounds S B hBsup) j t ht).1
        rows nset Pset D a (sourceGridCoefficient beta t) hrows hnset hP ha hD hβ
      apply (reconstructed_fixed_square_energy_le D t (fun d hd => (hD d hd).1) rows Pset a beta).trans
      convert hfix using 1 <;> (try dsimp only [E]) <;> first | rfl | ring
    have he := hybrid_square_dyad_energy S B hBsup j rows
      (fun t k => ∑ d ∈ hybridCommonBlock S N i t,
        ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d)
      (E / Td ^ 2) (div_nonneg hE (sq_nonneg _)) htEnergy
    calc
      _ ≤ (256 * Td) ^ 2 * (E / Td ^ 2) := he
      _ = 256 ^ 2 * E := by field_simp
  have hrow (k : Ideal Eis) (hk : k ∈ rows) :
      supportedHybridRow S Pset a beta k = ∑ j, ∑ i, F j i k := by
    rw [supportedHybridRow_reconstruct S Pset
      (fun p hp => ⟨(hS p hp).1,
        primaryIdealGenerator_ne_zero_ideal p.2 (hS p hp).2.2.1,
        (hS p hp).2.1, (hS p hp).2.2.1⟩)
      (fun P hPP => (hP P hPP).1.2) a beta k (hrows k hk).1]
    exact hybrid_dyadic_reindex S N B _
  calc
    _ = ∑ k ∈ rows, ‖∑ j, ∑ i, F j i k‖ ^ 2 :=
      Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
    _ ≤ ((Fintype.card (Fin (columnDyadicLength B + 1)) : ℝ) *
        (Fintype.card (Fin (columnDyadicLength N + 1)) : ℝ)) ^ 2 * (256 ^ 2 * E) :=
      finite_double_row_energy rows F (256 ^ 2 * E) (by positivity) hlabel
    _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, E]; ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

private theorem hybrid_log_cost_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2 ≤ C * (K * N * B) ^ ε := by
  let δ := ε / 9
  let A := 2 + 1 / (δ * Real.log 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A ^ 6, pow_pos hA 6, ?_⟩
  intro K N B hK hN hB
  let Q := K * N * B
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hQ0 : 0 < Q := by linarith
  have hKQ : K ≤ Q :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ K) hN).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hNQ : N ≤ Q :=
    (le_mul_of_one_le_left (by linarith : 0 ≤ N) hK).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hBQ : B ≤ Q := le_mul_of_one_le_left (by linarith)
    (one_le_mul_of_one_le_of_one_le hK hN)
  have hquad : K * (N * B) * N ≤ Q ^ 2 := by
    calc
      _ = Q * N := by dsimp only [Q]; ring
      _ ≤ Q * Q := mul_le_mul_of_nonneg_left hNQ hQ0.le
      _ = _ := by ring
  have hlog (Y : ℝ) (hY : 1 ≤ Y) (hYQ : Y ≤ Q) :
      (columnDyadicLength Y + 1 : ℝ) ≤ A * Q ^ δ := by
    exact (columnDyadicLength_small_power δ hδ Y hY).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hYQ hδ.le) hA.le)
  have hpow2 : (Q ^ 2) ^ δ = (Q ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hQ0.le 2 δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hpow9 : (Q ^ δ) ^ 9 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    dsimp only [δ]
    ring
  calc
    _ ≤ Q ^ δ * (Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ K * (N * B) * N) hquad hδ.le
      rw [hpow2] at hbase
      gcongr
      · exact hlog K hK hKQ
      · exact hlog N hN hNQ
      · exact hlog B hB hBQ
    _ = A ^ 6 * (Q ^ δ) ^ 9 := by ring
    _ = _ := by rw [hpow9]

theorem supportedHybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryIdealGenerator p.1 ≠ 0 ∧ primaryIdealGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := supportedHybridRow_energy_log (ε / 9) (by positivity)
  obtain ⟨C₁, hC₁, hlogs⟩ := hybrid_log_cost_bound ε hε
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hb := he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  apply hb.trans
  calc
    _ = C₀ * (K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2) *
        (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by ring
    _ ≤ C₀ * (C₁ * (K * N * B) ^ ε) * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hlogs K N B hK hN hB) hC₀.le)
            (by positivity)) (by linarith)) hs
    _ = _ := by ring

theorem hybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryIdealGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, he⟩ := supportedHybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta
  have hprod : ∀ p ∈ nset ×ˢ bset,
      Squarefree p.1 ∧ primaryIdealGenerator p.1 ≠ 0 ∧ primaryIdealGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpn, hpb⟩ := Finset.mem_product.mp hp
    exact ⟨(hn p.1 hpn).1.1, (hn p.1 hpn).1.2, (hb p.2 hpb).1,
      (hn p.1 hpn).2, (hb p.2 hpb).2⟩
  have hh := he K N B L hK hN hB rows (nset ×ˢ bset) Pset a beta hrows hprod hP ha
    (fun p hp => hbeta p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simpa only [supportedHybridRow_product] using hh

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

theorem hybrid_sharp_cubic_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      (K * N * B) ^ (ε / 2) * CubicSieve.sieveNorm N (2 * L) ≤
        C * (K * N * B * L) ^ ε * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := CubicSieve.sieveNorm_sharp (ε / 2) (by positivity)
  refine ⟨2 * C * (2 : ℝ) ^ (ε / 2), by positivity, ?_⟩
  intro K N B L hK hN hB hL
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  let Q := K * N * B * L
  have hQ0 : 0 < Q := by dsimp only [Q]; positivity
  have hKNB : K * N * B ≤ Q := le_mul_of_one_le_right (by positivity) hL
  have hNL : N * L ≤ Q := by
    have hKB : 1 ≤ K * B := one_le_mul_of_one_le_of_one_le hK hB
    have hh := le_mul_of_one_le_left (by positivity : 0 ≤ N * L) hKB
    convert hh using 1 <;> (try dsimp only [Q]) <;> first | rfl | ring
  have hdouble (t : ℝ) : (N * (2 * L)) ^ t = (2 : ℝ) ^ t * (N * L) ^ t := by
    rw [show N * (2 * L) = 2 * (N * L) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hshape : N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ) ≤
      2 * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
    rw [hdouble]
    have hh := mul_le_mul_of_nonneg_right h23 (Real.rpow_nonneg (by positivity : 0 ≤ N * L) (2 / 3 : ℝ))
    linarith
  have hcost : (K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2) ≤ Q ^ ε := by
    calc
      _ ≤ Q ^ (ε / 2) * Q ^ (ε / 2) := by
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hKNB (by positivity))
          (Real.rpow_le_rpow (by positivity) hNL (by positivity))
          (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hQ0.le _)
      _ = _ := by rw [← Real.rpow_add hQ0]; congr 1; ring
  have hh := hb N (2 * L) hN (by linarith)
  calc
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (2 * (N + L + (N * L) ^ (2 / 3 : ℝ)))) := by
      gcongr
    _ = (2 * C * (2 : ℝ) ^ (ε / 2)) *
        ((K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2)) * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
      rw [hdouble]
      ring
    _ ≤ _ := by gcongr

theorem supportedHybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryIdealGenerator p.1 ≠ 0 ∧ primaryIdealGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := supportedHybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows S Pset a beta hrows hS hP ha hbeta
  apply (he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

theorem hybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryIdealGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := hybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows nset bset Pset a beta hrows hn hb hP ha hbeta
  apply (he K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff
namespace InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

lemma actual_ideal_norm_pos (I : Ideal Eis) (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

theorem actual_residual_norm_width (I Q : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
      (Ideal.absNorm (rowPowerfulPart I) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm (rowMaskPart I Q) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeMaskPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal Eis => (Ideal.absNorm J : ℝ))
    (row_powerful_mask_residual_product I Q hI)
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm (rowMaskPart I Q) : ℝ) * (Ideal.absNorm (rowResidualPart I Q) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
          (Ideal.absNorm (rowPowerfulPart I) : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

theorem actual_common_width_charge {ι : Type*} [Fintype ι]
    (I F Q : Ideal Eis) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * Q)
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I Q) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hm := actual_ideal_norm_pos (rowMaskPart I Q)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)
  have he := rowResidualPart_norm I Q hI
  calc
    _ ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
        ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowMaskPart I Q) : ℝ)^2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
        (sq_nonneg _)
    _ = _ := by rw [he]; field_simp

theorem actual_common_width_charge_label_puncture {ι : Type*} [Fintype ι]
    (I F rho S : Ideal Eis) (hI : I ≠ 0) (hF : F ≠ 0) (hrho : rho ≠ 0) (hS : S ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (S * F * rho))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (S * F * rho)) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I (S * F * rho)) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  convert actual_common_width_charge I F (S * F * rho) hI
    (mul_ne_zero (mul_ne_zero hS hF) hrho) P hcop hpool hres e using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal Eis) : Ideal Eis := ∏ i, p i

theorem slotTupleProduct_injective_on
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) :
    Set.InjOn (slotTupleProduct (ι := ι)) {p | ∀ i, p i ∈ L i} := by
  intro p hpL q hqL he
  funext i
  change (∏ i, p i) = ∏ i, q i at he
  have hdiv : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, hj, hd⟩ := ((hp i (p i) (hpL i)).dvd_finsetProd_iff q).mp hdiv
  have hpq : p i = q j := associated_iff_eq.mp
    ((hp i (p i) (hpL i)).associated_of_dvd (hp j (q j) (hqL j)) hd)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hL hne) (hpL i) (hpq.symm ▸ hqL j)
  simpa only [← hij] using hpq

omit [DecidableEq ι] in
theorem slotTupleProduct_admissible
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hgen : ∀ i, ∀ P ∈ L i, primaryIdealGenerator P ≠ 0)
    (p : ι → Ideal Eis) (hpL : ∀ i, p i ∈ L i) :
    CubicSieve.Admissible (slotTupleProduct p) := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      have hpi := hp i (p i) (hpL i)
      have hpj := hp j (p j) (hpL j)
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime hpi).isMaximal hpi.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime hpj).isMaximal hpj.ne_zero
      apply (Ideal.isCoprime_of_isMaximal ?_).isRelPrime
      intro he
      exact Finset.disjoint_left.mp (hL hij) (hpL i) (he.symm ▸ hpL j)
    · intro i hi
      exact (hp i (p i) (hpL i)).squarefree
  · change primaryIdealGeneratorHom (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hgen i (p i) (hpL i))

def slotProductCoefficient (tuples : Finset (ι → Ideal Eis))
    (a : (ι → Ideal Eis) → ℂ) (P : Ideal Eis) : ℂ :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (a : (ι → Ideal Eis) → ℂ) (p : ι → Ideal Eis) (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact if_neg (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid


namespace InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_inherited_puncture_ne_zero
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    actualSecondInheritedPuncture m (actualSecondChild p u v x).1 ≠ 0 := by
  change ((m*cubicIdealGenerator x.quotient)*
    primaryIdealGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}))*
    primaryIdealGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) ≠ 0
  rw [show primaryIdealGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryIdealGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm (cubicIdealGenerator_ne_zero _ ht))
    (primeProduct_ne_zero p hp _ _)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

lemma radicalGenerator_ne_zero (a : Eis) (ha : a ≠ 0) :
    cubicIdealGenerator (Ideal.span {a}).radical ≠ 0 := by
  apply cubicIdealGenerator_ne_zero
  intro hz
  apply Ideal.span_singleton_eq_bot.not.mpr ha
  apply le_antisymm _ bot_le
  exact (Ideal.le_radical : (Ideal.span {a} : Ideal Eis) ≤ (Ideal.span {a}).radical).trans (le_of_eq hz)

def actualSecondPunctureWidth (Z : ℝ) (m : Eis) (γ : OuterTriple) : ℝ :=
  Real.logb Z (‖ringComplex (actualSecondInheritedRadicalPuncture m γ)‖^2)

include hp in
theorem actual_second_puncture_width_bound
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_budget p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ hB hT hG hD

include hp in

theorem actual_second_child_margins
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_bound p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ hB hT hG hD
  unfold decrease
  linarith

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_row_decrease
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z M ell A t g theta V j eta d : ℝ) (hZ : 1 < Z)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hterminal : d ≤ ell+V) (heta : eta ≤ d/16)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    3*d/2 ≤ M-childM M ell A t g theta V j eta :=
  child_row_decrease hA ht (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hterminal heta

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid


namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_radical_puncture_q0_norm
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ringComplex (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,SchwartzPlanePoisson.span_finset_prime_product]
  rw [ringComplex_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,span_cubicIdealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _))
    (sourceIdeal_ne_zero p hp _) Ideal.le_radical

include hp in

theorem actual_second_inherited_puncture_q0_norm
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ringComplex (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (cubicIdealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_q0_norm p hp hpr x hE u v
    (m*cubicIdealGenerator x.quotient) hm'
  change ‖ringComplex (actualSecondRadicalPuncture
    (m*cubicIdealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*cubicIdealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,span_cubicIdealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)) (primeProductNorm_pos p hp _).le

include hp in

theorem actual_second_q0_cube_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ B := by
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ B
  rw [←ringComplex_norm_sq_eq_absNorm_span]
  exact (cube_label_norm_bounds p hp _ _ _ _ _ x.cube.support_pos B hB h1 h2).2.1

include hp in
theorem actual_second_puncture_power_from_cubes
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖ringComplex (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  have hb := actual_second_q0_cube_bound p hp x u v _ (Real.rpow_pos_of_pos hZ _).le h1 h2
  apply (actual_second_inherited_puncture_q0_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

include hp in
theorem actual_second_puncture_width_from_cubes
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_from_cubes p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ h1 h2 hT hG hD

include hp in

theorem actual_second_child_margins_from_cubes
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_from_cubes p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ h1 h2 hT hG hD
  unfold decrease
  linarith

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1< Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

lemma actual_cell_label_nonneg (Z B j eta : ℝ) (d : BlockIndex)
    (hZ : 1< Z) (hB : 0≤ B) (hj : 0≤ j) (heta : 0≤ eta) :
    0≤ actualCellLabelExponent Z B j eta d := by
  have h1 := secondCellExponent_nonneg Z d 1 hZ
  have h2 := secondCellExponent_nonneg Z d 2 hZ
  unfold actualCellLabelExponent secondFormalLabel
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤ outerNorms p x i ∧
      outerNorms p x i≤ Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0< Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤ secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,lambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1< Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤ A) (ht : 0≤ t) (hV : 0≤ V) (hj : 0≤ j) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Q)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤ Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

theorem actual_cell_child_total_upper {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z r ell V A B t j eta b : ℝ) (hZ : 1< Z)
    (hA : 0≤ A) (ht : 0≤ t) (hell : 0≤ ell) (hV : 0≤ V) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hb : 1≤ b) (hthreshold : b≤ Z^(6*eta))
    (hgeom : ∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*Z^(r-A-B-t))
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖ringComplex (jLabel p x.cube.support
      (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d≤(r+3*ell+V)+15*eta := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hgt := actual_second_common_center p hp x (hs.second_divisor x hxs) Z
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD)
  have hj := actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ
  have hd : d∈keys p source := (mem_keys_iff p source d).mpr ⟨x,hx⟩
  have hc := second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hb
    (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  unfold childF decrease actualCellClipping
  linarith

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (Ideal O) :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

lemma actual_cell_labels_cover {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem actual_cell_labels_bound (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1< Z) (hbin : 2≤ Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤ Z^(B+eta))
    (hJ : ∀x∈source,‖ringComplex (jLabel p x.cube.support
      (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(j+eta)) :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤ Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

theorem actual_cell_squarefree_labels (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1< Z) (hbin : 2≤ Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤ Z^(B+eta))
    (hJ : ∀x∈source,‖ringComplex (jLabel p x.cube.support
      (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(j+eta)) :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

theorem actual_cell_nonzero_weight_label (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (hw : actualSecondSignedWeight p hg Ψ m ray x≠0) :
    (actualSecondChild p 1 1 x).2.1∈(actualCellLabels p source d).filter Squarefree := by
  have hxs := cell_subset p source d hx
  exact Finset.mem_filter.mpr ⟨actual_cell_labels_cover p source d x hx,
    actual_second_nonzero_weight_squarefree p hcop hg Ψ m ray x
      (hs.common_disjoint x hxs) (hs.second_divisor x hxs) hw 1 1⟩

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_label_support {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z B j eta : ℝ) (hZ : 1< Z) (hbin : 2≤ Z^eta)
    (hC : primeProductNorm p x.firstCommon≤ Z^(B+eta))
    (hJ : ‖ringComplex (jLabel p x.cube.support
      (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤ Z^(actualCellLabelExponent Z B j eta d) :=
  actual_cell_child_label_power p hp source hk d x hx u v Z B j eta hZ hbin hC hJ

theorem actual_cell_correlated_row_support
    (hpr : ∀i,lambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1< Z)
    (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hL0 : 0≤ L)
    (hd : ‖ringComplex (primeSubsetGenerator (fun i=> Ideal.span {p i}) x.firstDivisor)‖^2≤ Z^(delta+eta))
    (hL : L≤ Z^(r-A-B-t+4*eta))
    (hgate : x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=> Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    (actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (Z^(childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)) := by
  have hE := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr := second_correlated_radius_childM p hp
    (primeSubsetGenerator (fun i=> Ideal.span {p i}) x.firstDivisor) x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 hd (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  apply (actual_second_row_ball p hp hpr x u v _).mp
  have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p hp x) _ _).mp hgate
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p hp x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

omit hp in

lemma actual_child_row_length_nonneg (Z M : ℝ) (hZ : 1< Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) : 0≤ M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) k).mp hk
  simp only [one_mul] at hb
  have hk0 : k≠0 := (Finset.mem_erase.mp hk).1
  have hn := SchwartzPlanePoisson.one_le_eisenstein_norm_sq k hk0
  have hpow : Z^(0:ℝ)≤ Z^M := by simpa only [Real.rpow_zero,one_mul] using hn.trans hb.2
  exact (Real.rpow_le_rpow_left_iff hZ).mp hpow

theorem actual_cell_row_decrease {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1< Z)
    (hA : 0≤ A) (ht : 0≤ t) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hterminal : cutoff≤ ell+V) (hsmall : eta≤ cutoff/16)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖ringComplex (jLabel p x.cube.support
      (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤ M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,lambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_margins
    (hpr : ∀i,lambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1< Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤ A) (ht : 0≤ t) (hV : 0≤ V) (hj : 0≤ j) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Q)
    (h1 : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤ Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤ actualSecondPunctureWidth Z m γ ∧
    ‖ringComplex (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (SchwartzPlanePoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

omit hp in

theorem actual_child_enlarged_row_bounds (Z M : ℝ) (hZ : 1< Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) :
    k≠0 ∧ ‖ringComplex k‖^2≤ Z^M ∧ 0≤ M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ k).mp hk
  simp only [one_mul] at hb
  exact ⟨(Finset.mem_erase.mp hk).1,hb.2,actual_child_row_length_nonneg Z M hZ k hk⟩

omit hp in

theorem actual_child_size_caps (F M Q z c cap : ℝ)
    (hinv : CanonicalMargins F M Q z c) (hM : 0≤ M) (hQ : 0≤ Q) (hz : 0≤ z)
    (hc : 0≤ c) (hF : F≤ cap) : M≤ cap ∧ Q≤ cap ∧ z≤ cap := by
  obtain ⟨h1,h2⟩ := hinv
  constructor
  · linarith
  constructor <;> linarith

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

lemma actual_cell_row_radius_pos (Z M ell A t V j eta : ℝ) (d : BlockIndex) (hZ : 0< Z) :
    0< actualCellRowRadius Z M ell A t V j eta d := Real.rpow_pos_of_pos hZ _

theorem actual_cell_correlated_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,lambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1< Z)
    (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hL0 : 0≤ L)
    (hd : ∀x∈source,‖ringComplex (primeSubsetGenerator (fun i=> Ideal.span {p i}) x.firstDivisor)‖^2≤ Z^(delta+eta))
    (hL : L≤ Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=> Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs := cell_subset p source d hx
  exact (actual_second_row_ball p hp hpr x 1 1 _).mpr
    (actual_cell_correlated_row_support p hp hpr source hk d x hx 1 1
      Z M r ell V delta A B j t eta tau L hZ heta hbin hL0 (hd x hxs) hL (hgate x hxs))

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1< Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤ actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hp : ∀ i, p i ≠ 0 := fun i =>
    Ideal.span_singleton_eq_bot.not.mp (NeZero.ne (Ideal.span {p i}))
  have hr := actual_second_row_radius_one p hp (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)

end InverseMoment
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
