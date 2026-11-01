import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.AdelicKreinGeometry.ThreePrimesCarryTheWholeAffineState
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexOfABohrSeries
import GaloisForLFunctions.HeckeKreinToeplitz.Index.WeightedGrams
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWeilKernelHasInfinitelyManyPositiveSquares
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# Two primes and bounded translations carry the full affine Weil index

A subgroup with dense logarithms retains all Weil negative squares after a
positive constant is subtracted, and gains exactly one square. For finite index,
a normalized finite character filter removes every off-critical pair. Bohr
averages then remove the critical characters, whose frequencies are nonzero.
The resulting mass-one families have vanishing energy and fixed cross terms.
A block Gram limit supplies the independent negative constant direction.

For principal-unit slopes, equal half-weights at translations `0,1` compress the
native p-adic affine state to `ratCorr-c/2`. Thus two fixed primes outside `p`
already carry index `κ(ratCorr)+1` with translations in `ℤ[1/(qr)]`. Every such
translation has p-adic norm at most one; expanding translations are unnecessary.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

section Filter

variable {G J : Type*} [CommGroup G] [Fintype J] [DecidableEq J]

/-- Support of the convolution of the two-point character filters. -/
private def filterPoint (u : J → G) (e : J → Fin 2) : G :=
  ∏ j, if e j = 0 then 1 else u j

/-- Each factor has mass one and vanishes at its designated character. -/
private def filterWeight (χ : J → G →* ℂ) (u : J → G) (e : J → Fin 2) : ℂ :=
  ∏ j, if e j = 0 then -χ j (u j) / (1 - χ j (u j)) else (1 - χ j (u j))⁻¹

/-- Character evaluation turns convolution into multiplication. -/
private theorem charEval_filter (χ : J → G →* ℂ) (u : J → G) (ψ : G →* ℂ) :
    charEval ψ (filterPoint u) (filterWeight χ u) =
      ∏ j, (ψ (u j) - χ j (u j)) / (1 - χ j (u j)) := by
  classical
  simp only [charEval_apply, filterPoint, filterWeight, map_prod]
  calc
    ∑ e : J → Fin 2, (∏ j, if e j = 0 then -χ j (u j) / (1 - χ j (u j))
          else (1 - χ j (u j))⁻¹) * (∏ j, ψ (if e j = 0 then 1 else u j))
      = ∑ e : J → Fin 2, ∏ j,
          (if e j = 0 then -χ j (u j) / (1 - χ j (u j)) else (1 - χ j (u j))⁻¹) *
            ψ (if e j = 0 then 1 else u j) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.prod_mul_distrib]
    _ = ∏ j, ∑ b : Fin 2,
          (if b = 0 then -χ j (u j) / (1 - χ j (u j)) else (1 - χ j (u j))⁻¹) *
            ψ (if b = 0 then 1 else u j) := by rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Fin.sum_univ_two]
      norm_num
      ring

private theorem filter_mass_one (χ : J → G →* ℂ) (u : J → G)
    (hu : ∀ j, χ j (u j) ≠ 1) :
    ∑ e : J → Fin 2, filterWeight χ u e = 1 := by
  have h := charEval_filter χ u (1 : G →* ℂ)
  simp only [charEval_apply, MonoidHom.one_apply, mul_one] at h
  rw [h]
  exact Finset.prod_eq_one fun j _ => div_self (sub_ne_zero.mpr (hu j).symm)

private theorem filter_kills (χ : J → G →* ℂ) (u : J → G) (j : J) :
    charEval (χ j) (filterPoint u) (filterWeight χ u) = 0 := by
  classical
  rw [charEval_filter]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [sub_self, zero_div]

end Filter


section Means

variable {G J : Type*} [CommGroup G] [Fintype J] [DecidableEq J]

private theorem charEval_product {A B : Type*} [Fintype A] [Fintype B]
    (χ : G →* ℂ) (x : A → G) (y : B → G) (c : A → ℂ) (d : B → ℂ) :
    charEval χ (fun ab : A × B => x ab.1 * y ab.2) (fun ab => c ab.1 * d ab.2) =
      charEval χ x c * charEval χ y d := by
  simp only [charEval_apply, Fintype.sum_prod_type, map_mul, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private def meanWeight (T : ℕ) (_ : Fin T → Fin T) : ℂ := ((T : ℂ) ^ T)⁻¹

private theorem charEval_mean (ψ : ℕ → G →* ℂ) (hzero : ψ 0 = 1) (T j : ℕ) :
    charEval (ψ j) (boxPoint ψ T) (meanWeight T) = boxMean ψ T 0 j := by
  simp only [charEval_apply, meanWeight, boxMean, hzero, MonoidHom.one_apply,
    map_one, one_mul, Finset.mul_sum]

private theorem mean_mass_one (ψ : ℕ → G →* ℂ)
    (hψ : ∀ j, IsUnitaryChar (ψ j)) (hzero : ψ 0 = 1) (T : ℕ) :
    ∑ e : Fin T → Fin T, meanWeight T e = 1 := by
  have h := (charEval_mean ψ hzero T 0).trans (boxMean_self hψ T 0)
  simpa only [hzero, charEval_apply, MonoidHom.one_apply, mul_one] using h

private def filteredMeanPoint (_χ : J → G →* ℂ) (u : J → G)
    (ψ : ℕ → G →* ℂ) (T : ℕ) (e : (J → Fin 2) × (Fin T → Fin T)) : G :=
  filterPoint u e.1 * boxPoint ψ T e.2

private def filteredMeanWeight (χ : J → G →* ℂ) (u : J → G)
    (T : ℕ) (e : (J → Fin 2) × (Fin T → Fin T)) : ℂ :=
  filterWeight χ u e.1 * meanWeight T e.2

private theorem filteredMean_mass_one (χ : J → G →* ℂ) (u : J → G)
    (hu : ∀ j, χ j (u j) ≠ 1) (ψ : ℕ → G →* ℂ)
    (hψ : ∀ j, IsUnitaryChar (ψ j)) (hzero : ψ 0 = 1) (T : ℕ) :
    ∑ e, filteredMeanWeight χ u T e = 1 := by
  simp only [filteredMeanWeight, Fintype.sum_prod_type,
    ← Finset.mul_sum, filter_mass_one χ u hu, mean_mass_one ψ hψ hzero, mul_one]

private theorem filteredMean_kills (χ : J → G →* ℂ) (u : J → G)
    (ψ : ℕ → G →* ℂ) (T : ℕ) (j : J) :
    charEval (χ j) (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T) = 0 := by
  rw [show filteredMeanPoint χ u ψ T =
    (fun e : (J → Fin 2) × (Fin T → Fin T) => filterPoint u e.1 * boxPoint ψ T e.2) from rfl]
  rw [show filteredMeanWeight χ u T =
    (fun e : (J → Fin 2) × (Fin T → Fin T) => filterWeight χ u e.1 * meanWeight T e.2) from rfl]
  rw [charEval_product, filter_kills, zero_mul]

private theorem filteredMean_unitary_eval (χ : J → G →* ℂ) (u : J → G)
    (ψ : ℕ → G →* ℂ) (hzero : ψ 0 = 1) (T j : ℕ) :
    charEval (ψ j) (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T) =
      charEval (ψ j) (filterPoint u) (filterWeight χ u) * boxMean ψ T 0 j := by
  change charEval (ψ j)
    (fun e : (J → Fin 2) × (Fin T → Fin T) => filterPoint u e.1 * boxPoint ψ T e.2)
    (fun e => filterWeight χ u e.1 * meanWeight T e.2) = _
  rw [charEval_product, charEval_mean ψ hzero]

private theorem tendsto_filteredMean_eval (χ : J → G →* ℂ) (u : J → G)
    (ψ : ℕ → G →* ℂ) (hψ : ∀ j, IsUnitaryChar (ψ j))
    (hinj : Function.Injective ψ) (hzero : ψ 0 = 1) (j : ℕ) :
    Tendsto (fun T => charEval (ψ (j + 1))
      (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T)) atTop (𝓝 0) := by
  simp_rw [filteredMean_unitary_eval χ u ψ hzero]
  simpa using (tendsto_boxMean hψ hinj 0 (j + 1)).const_mul
    (charEval (ψ (j + 1)) (filterPoint u) (filterWeight χ u))

private theorem norm_filteredMean_eval_le (χ : J → G →* ℂ) (u : J → G)
    (ψ : ℕ → G →* ℂ) (hψ : ∀ j, IsUnitaryChar (ψ j))
    (hzero : ψ 0 = 1) {T : ℕ} (hT : 0 < T) (j : ℕ) :
    ‖charEval (ψ j) (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T)‖ ≤
      ∑ e : J → Fin 2, ‖filterWeight χ u e‖ := by
  rw [filteredMean_unitary_eval χ u ψ hzero, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_boxMean_le_one hψ hT 0 j)).trans
    (norm_charEval_le hψ (filterPoint u) (filterWeight χ u) j)

end Means

section Energy

variable {G J : Type*} [CommGroup G] [Fintype J] [DecidableEq J]

/-- Absolute summability makes the annihilated Bohr energy tend to zero. -/
private theorem tendsto_filteredMean_bohr_energy
    (χ : J → G →* ℂ) (u : J → G) (ψ : ℕ → G →* ℂ)
    (hψ : ∀ j, IsUnitaryChar (ψ j)) (hinj : Function.Injective ψ) (hzero : ψ 0 = 1)
    {a : ℕ → ℝ} (ha : Summable a) :
    Tendsto (fun T => hermQuad (gram (bohrSum (fun j => ψ (j + 1)) a)
      (filteredMeanPoint χ u ψ T)) (filteredMeanWeight χ u T)) atTop (𝓝 0) := by
  simp_rw [hermQuad_gram_bohrSum (fun j => hψ (j + 1)) ha]
  let C : ℝ := ∑ e : J → Fin 2, ‖filterWeight χ u e‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlim : ∀ j, Tendsto (fun T => a j * normSq (charEval (ψ (j + 1))
      (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T))) atTop (𝓝 0) := by
    intro j
    simpa [Complex.normSq_eq_norm_sq] using
      ((tendsto_filteredMean_eval χ u ψ hψ hinj hzero j).norm.pow 2).const_mul (a j)
  have hb : ∀ᶠ T in atTop, ∀ j,
      ‖a j * normSq (charEval (ψ (j + 1)) (filteredMeanPoint χ u ψ T)
        (filteredMeanWeight χ u T))‖ ≤ |a j| * C ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with T hT j
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (normSq_nonneg _), Complex.normSq_eq_norm_sq]
    have he := norm_filteredMean_eval_le χ u ψ hψ hzero hT (j + 1)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he 2) (abs_nonneg _)
  have ht := tendsto_tsum_of_dominated_convergence
    ((summable_abs_iff.mpr ha).mul_right (C ^ 2)) hlim hb
  simpa using ht

private theorem bohr_packet_cross {A : Type*} [Fintype A]
    (ψ : ℕ → G →* ℂ) (hψ : ∀ j, IsUnitaryChar (ψ j))
    {a : ℕ → ℝ} (ha : Summable a) (x : A → G) (c : A → ℂ) (g : G) :
    ∑ i, c i * bohrSum ψ a (g⁻¹ * x i) =
      ∑' j, (a j : ℂ) * conj (ψ j g) * charEval (ψ j) x c := by
  have hs (i : A) : Summable (fun j => c i * ((a j : ℂ) * ψ j (g⁻¹ * x i))) :=
    (summable_coeff_mul ha (fun j => (hψ j _).le)).mul_left (c i)
  calc
    ∑ i, c i * bohrSum ψ a (g⁻¹ * x i)
        = ∑ i, ∑' j, c i * ((a j : ℂ) * ψ j (g⁻¹ * x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [bohrSum, tsum_mul_left]
    _ = ∑' j, ∑ i, c i * ((a j : ℂ) * ψ j (g⁻¹ * x i)) :=
      (Summable.tsum_finsetSum fun i _ => hs i).symm
    _ = _ := by
      apply tsum_congr
      intro j
      simp only [unitary_inv_mul hψ, charEval_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The same averaging kills interaction with every fixed point. -/
private theorem tendsto_filteredMean_bohr_cross
    (χ : J → G →* ℂ) (u : J → G) (ψ : ℕ → G →* ℂ)
    (hψ : ∀ j, IsUnitaryChar (ψ j)) (hinj : Function.Injective ψ) (hzero : ψ 0 = 1)
    {a : ℕ → ℝ} (ha : Summable a) (g : G) :
    Tendsto (fun T => ∑ i, filteredMeanWeight χ u T i *
      bohrSum (fun j => ψ (j + 1)) a (g⁻¹ * filteredMeanPoint χ u ψ T i))
      atTop (𝓝 0) := by
  simp_rw [bohr_packet_cross _ (fun j => hψ (j + 1)) ha]
  let C : ℝ := ∑ e : J → Fin 2, ‖filterWeight χ u e‖
  have hlim : ∀ j, Tendsto (fun T => (a j : ℂ) * conj (ψ (j + 1) g) *
      charEval (ψ (j + 1)) (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T))
      atTop (𝓝 0) := by
    intro j
    simpa using (tendsto_filteredMean_eval χ u ψ hψ hinj hzero j).const_mul
      ((a j : ℂ) * conj (ψ (j + 1) g))
  have hb : ∀ᶠ T in atTop, ∀ j,
      ‖(a j : ℂ) * conj (ψ (j + 1) g) *
        charEval (ψ (j + 1)) (filteredMeanPoint χ u ψ T) (filteredMeanWeight χ u T)‖
      ≤ |a j| * C := by
    filter_upwards [eventually_ge_atTop 1] with T hT j
    rw [norm_mul, norm_mul, Complex.norm_conj, hψ, Complex.norm_real,
      Real.norm_eq_abs, mul_one]
    exact mul_le_mul_of_nonneg_left
      (norm_filteredMean_eval_le χ u ψ hψ hzero hT (j + 1)) (abs_nonneg _)
  have ht := tendsto_tsum_of_dominated_convergence
    ((summable_abs_iff.mpr ha).mul_right C) hlim hb
  simpa using ht

end Energy

section Characters

variable {G : Type*} [CommGroup G]

/-- Arbitrarily small positive scales separate all complex logarithmic characters. -/
private theorem logChar_injective_of_small (ell : G →* Multiplicative ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u, 0 < scale ell u ∧ scale ell u < ε) :
    Function.Injective (logChar ell) := by
  intro a b hab
  let D : ℝ := ‖a - b‖ + 1
  have hD : 0 < D := by positivity
  obtain ⟨u, hu0, hu1⟩ := hsmall (2 * Real.pi / D) (by positivity)
  apply eq_of_cexp_mul_eq hu0
  · calc ‖a - b‖ * scale ell u ≤ D * scale ell u := by
           apply mul_le_mul_of_nonneg_right _ hu0.le
           dsimp [D]
           linarith only [norm_nonneg (a - b)]
         _ < D * (2 * Real.pi / D) := mul_lt_mul_of_pos_left hu1 hD
         _ = 2 * Real.pi := mul_div_cancel₀ _ hD.ne'
  · exact congrArg (fun chi : G →* ℂ => chi u) hab

private def prependTrivial (ψ : ℕ → G →* ℂ) : ℕ → G →* ℂ
  | 0 => 1
  | j + 1 => ψ j

private theorem prependTrivial_injective {ψ : ℕ → G →* ℂ}
    (hinj : Function.Injective ψ) (hnone : ∀ j, ψ j ≠ 1) :
    Function.Injective (prependTrivial ψ) := by
  intro i j h
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j => exact (hnone j h.symm).elim
  | succ i =>
    cases j with
    | zero => exact (hnone i h).elim
    | succ j => exact congrArg Nat.succ (hinj h)

private theorem prependTrivial_unitary {ψ : ℕ → G →* ℂ}
    (hψ : ∀ j, IsUnitaryChar (ψ j)) : ∀ j, IsUnitaryChar (prependTrivial ψ j) := by
  intro j
  cases j with
  | zero => intro u; simp [prependTrivial]
  | succ j => exact hψ j

end Characters


section PairRemoval

variable {G A J : Type*} [CommGroup G] [Fintype A] [Fintype J]

private theorem pair_packet_cross_zero (χ : G →* ℂ) (w : ℂ) (x : A → G) (c : A → ℂ)
    (hχ : charEval χ x c = 0) (hχr : charEval (reflectChar χ) x c = 0) (g : G) :
    ∑ i, c i * pairKernel χ w (g⁻¹ * x i) = 0 := by
  have he : ∑ i, c i * pairKernel χ w (g⁻¹ * x i) =
      w * χ g⁻¹ * charEval χ x c + conj w * reflectChar χ g⁻¹ *
        charEval (reflectChar χ) x c := by
    simp only [pairKernel, map_mul, mul_add, Finset.sum_add_distrib,
      charEval_apply, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he, hχ, hχr, mul_zero, mul_zero, add_zero]

private theorem pair_packet_energy_zero (χ : G →* ℂ) (w : ℂ) (x : A → G) (c : A → ℂ)
    (hχ : charEval χ x c = 0) : hermQuad (gram (pairKernel χ w) x) c = 0 := by
  rw [hermQuad_gram_pairKernel, hχ, mul_zero, zero_mul]
  simp

/-- Killing both characters removes a pair from every fixed-point interaction. -/
private theorem packet_cross_eq_of_pairs (K P : G → ℂ)
    (χ : J → G →* ℂ) (w : J → ℂ)
    (hrep : ∀ g, K g = P g + ∑ j, pairKernel (χ j) (w j) g)
    (x : A → G) (c : A → ℂ)
    (hχ : ∀ j, charEval (χ j) x c = 0)
    (hχr : ∀ j, charEval (reflectChar (χ j)) x c = 0) (g : G) :
    ∑ i, c i * K (g⁻¹ * x i) = ∑ i, c i * P (g⁻¹ * x i) := by
  simp only [hrep, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hz : ∑ j, ∑ i, c i * pairKernel (χ j) (w j) (g⁻¹ * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact pair_packet_cross_zero (χ j) (w j) x c (hχ j) (hχr j) g
  rw [hz, add_zero]

/-- The annihilator removes the finite paired part from self-energy. -/
private theorem packet_energy_eq_of_pairs (K P : G → ℂ)
    (χ : J → G →* ℂ) (w : J → ℂ)
    (hrep : ∀ g, K g = P g + ∑ j, pairKernel (χ j) (w j) g)
    (x : A → G) (c : A → ℂ)
    (hχ : ∀ j, charEval (χ j) x c = 0) :
    hermQuad (gram K x) c = hermQuad (gram P x) c := by
  have he : K = fun g => P g + ∑ j, pairKernel (χ j) (w j) g := funext hrep
  rw [he, hermQuad_gram_add, hermQuad_gram_sum]
  have hz : ∑ j, hermQuad (gram (pairKernel (χ j) (w j)) x) c = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact pair_packet_energy_zero (χ j) (w j) x c (hχ j)
  rw [hz, add_zero]

end PairRemoval

section Index

variable {G : Type*} [Group G]

private theorem packet_form_real {A : Type*} [Fintype A] {K : G → ℂ}
    (hK : IsHermKernel K) (x : A → G) (c : A → ℂ) :
    (∑ i, ∑ j, conj (c i) * K ((x i)⁻¹ * x j) * c j) =
      ((hermQuad (gram K x) c : ℝ) : ℂ) := by
  let z := ∑ i, ∑ j, conj (c i) * K ((x i)⁻¹ * x j) * c j
  have hz : conj z = z := by
    simp only [z, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hK, _root_.mul_inv_rev, inv_inv]
    ring
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  apply Complex.ext
  · simp only [hermQuad_gram, Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using him

private theorem mass_zero_constant_form {A : Type*} [Fintype A]
    (K : G → ℂ) (z : ℂ) (x : A → G) (c : A → ℂ) (hc : ∑ i, c i = 0) :
    hermQuad (gram (fun g => K g - z) x) c = hermQuad (gram K x) c := by
  rw [hermQuad_gram, hermQuad_gram]
  have he : ∑ i, ∑ j, conj (c i) * (K ((x i)⁻¹ * x j) - z) * c j =
      (∑ i, ∑ j, conj (c i) * K ((x i)⁻¹ * x j) * c j) -
      conj (∑ i, c i) * z * (∑ j, c j) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, map_sum,
      Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
  rw [he, hc, mul_zero, sub_zero]

private theorem polarIndex_sub_constant (K : G → ℂ) (z : ℂ) :
    GaloisForLFunctions.AdelicKreinGeometry.polarIndex (fun g => K g - z) =
      GaloisForLFunctions.AdelicKreinGeometry.polarIndex K := by
  simp only [GaloisForLFunctions.AdelicKreinGeometry.polarIndex]
  apply iSup_congr
  intro n
  apply iSup_congr
  intro x
  congr 1
  apply le_antisymm
  · apply GaloisForLFunctions.AdelicKreinGeometry.negIndexOn_le_of_hermQuad_le
    intro c hc
    exact (mass_zero_constant_form K z x c (LinearMap.mem_ker.mp hc)).ge
  · apply GaloisForLFunctions.AdelicKreinGeometry.negIndexOn_le_of_hermQuad_le
    intro c hc
    exact (mass_zero_constant_form K z x c (LinearMap.mem_ker.mp hc)).le

end Index


section ExtraSquare

variable {G : Type*} [Group G]

/-- A mass-one family of vanishing energy adds a negative scalar block to any polar family. -/
private theorem extra_square_from_null_packets {K : G → ℂ} (hK : IsHermKernel K)
    {d : ℝ} (hd : 0 < d) {I : ℕ → Type*} [∀ N, Fintype (I N)]
    (v : (N : ℕ) → I N → G) (c : (N : ℕ) → I N → ℂ)
    (hmass : ∀ N, ∑ i, c N i = 1)
    (hcross : ∀ g, Tendsto (fun N => ∑ i, c N i * K (g⁻¹ * v N i)) atTop (𝓝 0))
    (henergy : Tendsto (fun N => hermQuad (gram K (v N)) (c N)) atTop (𝓝 0))
    {m r : ℕ} (x : Fin m → G) (B : Matrix (Fin m) (Fin r) ℂ)
    (hB : ∀ j, ∑ i, B i j = 0)
    (hneg : ∀ a : Fin r → ℂ, a ≠ 0 → hermQuad (gram K x) (B *ᵥ a) < 0) :
    ((r + 1 : ℕ) : ℕ∞) ≤ negIndex (fun g => K g - (d : ℂ)) := by
  classical
  let L : G → ℂ := fun g => K g - (d : ℂ)
  have hL : IsHermKernel L := fun g => by
    simp only [L, hK g, map_sub, Complex.conj_ofReal]
  let A := gram L x
  let Sig : (N : ℕ) → Matrix (I N) (Fin 1) ℂ := fun N i _ => c N i
  let S : (N : ℕ) → Matrix (Fin m ⊕ I N) (Fin r ⊕ Fin 1) ℂ :=
    fun N => Matrix.fromBlocks B 0 0 (Sig N)
  let C : (N : ℕ) → Matrix (Fin m) (I N) ℂ := fun N i j => L ((x i)⁻¹ * v N j)
  let C' : (N : ℕ) → Matrix (I N) (Fin m) ℂ := fun N i j => L ((v N i)⁻¹ * x j)
  let E : (N : ℕ) → Matrix (I N) (I N) ℂ := fun N => gram L (v N)
  let H : ℕ → Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℂ :=
    fun N => (S N)ᴴ * gram L (Sum.elim x (v N)) * S N
  have hblock (N : ℕ) : gram L (Sum.elim x (v N)) =
      Matrix.fromBlocks A (C N) (C' N) (E N) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hH (N : ℕ) : H N = Matrix.fromBlocks (Bᴴ * A * B)
      (Bᴴ * C N * Sig N) ((Sig N)ᴴ * C' N * B) ((Sig N)ᴴ * E N * Sig N) := by
    simp only [H, hblock, S, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  let H0 : Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks (Bᴴ * A * B) 0 0 (Matrix.of fun _ _ => -(d : ℂ))
  have hBstar (j : Fin r) : ∑ i, conj (B i j) = 0 := by
    rw [← map_sum, hB, map_zero]
  have hres (g : G) : Tendsto (fun N => ∑ i, c N i * L (g⁻¹ * v N i))
      atTop (𝓝 (-(d : ℂ))) := by
    have he (N : ℕ) : (∑ i, c N i * L (g⁻¹ * v N i)) =
        (∑ i, c N i * K (g⁻¹ * v N i)) - (d : ℂ) := by
      simp only [L, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
    simp_rw [he]
    simpa using (hcross g).sub_const (d : ℂ)
  have hcrossB (j : Fin r) : Tendsto (fun N => (Bᴴ * C N * Sig N) j 0)
      atTop (𝓝 0) := by
    have he (N : ℕ) : (Bᴴ * C N * Sig N) j 0 =
        ∑ i, conj (B i j) * (∑ e, c N e * L ((x i)⁻¹ * v N e)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        C, Sig, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro e _
      ring
    simp_rw [he]
    have ht := tendsto_finsetSum Finset.univ (fun i _ => (hres (x i)).const_mul (conj (B i j)))
    simpa only [← Finset.sum_mul, hBstar, zero_mul] using ht
  have hC' (N : ℕ) : C' N = (C N)ᴴ := by
    ext i j
    simp only [C', C, Matrix.conjTranspose_apply, Complex.star_def]
    rw [← hL, _root_.mul_inv_rev, inv_inv]
  have hcrossB' (j : Fin r) : Tendsto (fun N => ((Sig N)ᴴ * C' N * B) 0 j)
      atTop (𝓝 0) := by
    have he (N : ℕ) : ((Sig N)ᴴ * C' N * B) 0 j = conj ((Bᴴ * C N * Sig N) j 0) := by
      rw [hC', ← Matrix.conjTranspose_conjTranspose B, ← Matrix.conjTranspose_mul,
        ← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_apply, Complex.star_def, Matrix.mul_assoc]
    simp_rw [he]
    simpa [Function.comp_def] using (Complex.continuous_conj.tendsto 0).comp (hcrossB j)
  have hscalar : Tendsto (fun N => ((Sig N)ᴴ * E N * Sig N) 0 0)
      atTop (𝓝 (-(d : ℂ))) := by
    have he (N : ℕ) : ((Sig N)ᴴ * E N * Sig N) 0 0 =
        ((hermQuad (gram K (v N)) (c N) : ℝ) : ℂ) - (d : ℂ) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        E, GaloisForLFunctions.HeckeKreinToeplitz.gram, Sig, L, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hsplit : (∑ i, ∑ j, conj (c N i) *
          (K ((v N i)⁻¹ * v N j) - (d : ℂ)) * c N j) =
          (∑ i, ∑ j, conj (c N i) * K ((v N i)⁻¹ * v N j) * c N j) -
          conj (∑ i, c N i) * (d : ℂ) * (∑ j, c N j) := by
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, map_sum,
          Finset.sum_mul, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
      rw [hsplit, hmass, map_one, one_mul, mul_one, packet_form_real hK]
    simp_rw [he]
    have ht := (Complex.continuous_ofReal.tendsto 0).comp henergy
    simpa [Function.comp_def] using ht.sub_const (d : ℂ)
  have hconv : ∀ i j, Tendsto (fun N => H N i j) atTop (𝓝 (H0 i j)) := by
    intro i j
    simp only [hH]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact tendsto_const_nhds
      | inr j => fin_cases j; simpa [H0] using hcrossB i
    | inr i =>
      cases j with
      | inl j => fin_cases i; simpa [H0] using hcrossB' j
      | inr j => fin_cases i; fin_cases j; simpa [H0] using hscalar
  have hH0 : H0.IsHermitian := by
    apply Matrix.IsHermitian.fromBlocks
    · simpa [A, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun M => Bᴴ * M * B) (gram_isHermitian hL x)
    · simp
    · ext i j; simp [Matrix.conjTranspose_apply]
  have hP : r ≤ hermNegIndex (Bᴴ * A * B) := by
    have hh := card_le_hermNegIndex_of_forall_neg (Bᴴ * A * B) LinearMap.id (fun a ha => by
      rw [LinearMap.id_apply, hermQuad_rect_conjugate]
      have hm : ∑ i, (B *ᵥ a) i = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, hB, zero_mul, Finset.sum_const_zero]
      change hermQuad (gram (fun g => K g - (d : ℂ)) x) (B *ᵥ a) < 0
      rw [mass_zero_constant_form K (d : ℂ) x _ hm]
      exact hneg a ha)
    simpa using hh
  have hsc : 1 ≤ hermNegIndex (Matrix.of fun _ _ : Fin 1 => -(d : ℂ)) := by
    have hh : hermQuad (Matrix.of fun _ _ : Fin 1 => -(d : ℂ)) ![1] < 0 := by
      simpa [hermQuad, Matrix.mulVec, dotProduct] using neg_neg_of_pos hd
    exact (one_le_negIndexOn (V := ⊤) Submodule.mem_top hh).trans (negIndexOn_le_hermNegIndex _ _)
  have hlimit : r + 1 ≤ hermNegIndex H0 :=
    (add_le_add hP hsc).trans (GaloisForLFunctions.AdelicKreinGeometry.hermNegIndex_add_le_fromBlocks _ _)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH0 hconv).exists
  have hcomp : hermNegIndex (H N) ≤ hermNegIndex (gram L (Sum.elim x (v N))) :=
    GaloisForLFunctions.ArithmeticCastelnuovoSeveri.negIndex_compress_le _ (S N)
  exact (Nat.cast_le.mpr ((hlimit.trans hN).trans hcomp)).trans
    (hermNegIndex_gram_le_negIndex L (Sum.elim x (v N)))

end ExtraSquare


section ConstantIndexLaw

open GaloisForLFunctions.AdelicKreinGeometry

variable {G : Type*} [Group G] {K : G → ℂ}

private theorem polar_family_extra_square (hK : IsHermKernel K) {d : ℝ} (hd : 0 < d)
    {I : ℕ → Type*} [∀ N, Fintype (I N)]
    (v : (N : ℕ) → I N → G) (c : (N : ℕ) → I N → ℂ)
    (hmass : ∀ N, ∑ i, c N i = 1)
    (hcross : ∀ g, Tendsto (fun N => ∑ i, c N i * K (g⁻¹ * v N i)) atTop (𝓝 0))
    (henergy : Tendsto (fun N => hermQuad (gram K (v N)) (c N)) atTop (𝓝 0))
    {m : ℕ} (x : Fin m → G) :
    (negIndexOn (gram K x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) + 1 ≤
      negIndex (fun g => K g - (d : ℂ)) := by
  classical
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram K x) (LinearMap.ker (totalMass (Fin m)))
  let r := Module.finrank ℂ W
  let bW := Module.finBasis ℂ W
  let B : Matrix (Fin m) (Fin r) ℂ := fun i j => (bW j : Fin m → ℂ) i
  have hB (j : Fin r) : ∑ i, B i j = 0 := LinearMap.mem_ker.mp (hWV (bW j).2)
  have hneg (a : Fin r → ℂ) (ha : a ≠ 0) : hermQuad (gram K x) (B *ᵥ a) < 0 := by
    have hmem : B *ᵥ a = (bW.equivFun.symm a : Fin m → ℂ) := by
      ext i
      simp only [Matrix.mulVec, dotProduct, B, Module.Basis.equivFun_symm_apply,
        Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have ha0 : (bW.equivFun.symm a : Fin m → ℂ) ≠ 0 := fun h =>
      ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
    rw [hmem]
    have hh := hW _ (bW.equivFun.symm a).2 ha0
    rw [hermQuad_neg] at hh
    linarith only [hh]
  have hh := extra_square_from_null_packets hK hd v c hmass hcross henergy x B hB hneg
  simpa only [r, Nat.cast_add, Nat.cast_one, hWr] using hh

/-- Null mass-one families attain the one-square hyperplane bound after subtraction. -/
private theorem negIndex_sub_constant_of_null_packets (hK : IsHermKernel K)
    {d : ℝ} (hd : 0 < d) {I : ℕ → Type*} [∀ N, Fintype (I N)]
    (v : (N : ℕ) → I N → G) (c : (N : ℕ) → I N → ℂ)
    (hmass : ∀ N, ∑ i, c N i = 1)
    (hcross : ∀ g, Tendsto (fun N => ∑ i, c N i * K (g⁻¹ * v N i)) atTop (𝓝 0))
    (henergy : Tendsto (fun N => hermQuad (gram K (v N)) (c N)) atTop (𝓝 0)) :
    negIndex (fun g => K g - (d : ℂ)) = polarIndex K + 1 := by
  refine le_antisymm ?_ ?_
  · simpa only [polarIndex_sub_constant] using
      negIndex_le_polarIndex_add_one (fun g => K g - (d : ℂ))
  · rcases eq_or_ne (negIndex (fun g => K g - (d : ℂ))) ⊤ with ht | ht
    · rw [ht]
      exact le_top
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp ht
    have hfam : ∀ (m : ℕ) (x : Fin m → G),
        negIndexOn (gram K x) (LinearMap.ker (totalMass (Fin m))) + 1 ≤ M := by
      intro m x
      have hh := polar_family_extra_square hK hd v c hmass hcross henergy x
      rw [← hM] at hh
      exact_mod_cast hh
    have h1 : 1 ≤ M := by have := hfam 0 (fun i => i.elim0); omega
    have hall : ∀ (m : ℕ) (x : Fin m → G),
        (negIndexOn (gram K x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) ≤
          ((M - 1 : ℕ) : ℕ∞) := by
      intro m x
      exact Nat.cast_le.mpr (by have := hfam m x; omega)
    calc polarIndex K + 1 ≤ ((M - 1 : ℕ) : ℕ∞) + 1 :=
           add_le_add (iSup₂_le hall) le_rfl
         _ = negIndex (fun g => K g - (d : ℂ)) := by
           rw [← hM]
           norm_cast
           omega

end ConstantIndexLaw


section SpectralIndex

open GaloisForLFunctions.AdelicKreinGeometry

variable {G J : Type*} [CommGroup G] [Fintype J]

/-- A finite filter removes the nonunitary modes before averaging the nonzero unitary modes. -/
private theorem negIndex_sub_constant_of_spectral_decomposition
    {K : G → ℂ} (hK : IsHermKernel K) (ψ : ℕ → G →* ℂ)
    (hψ : ∀ j, IsUnitaryChar (ψ j)) (hinj : Function.Injective ψ)
    (hnone : ∀ j, ψ j ≠ 1) {a : ℕ → ℝ} (ha : Summable a)
    (χ : J → G →* ℂ) (hχ : ∀ j, χ j ≠ 1) (w : J → ℂ)
    (hrep : ∀ g, K g = bohrSum ψ a g + ∑ j, pairKernel (χ j) (w j) g)
    {d : ℝ} (hd : 0 < d) :
    negIndex (fun g => K g - (d : ℂ)) = polarIndex K + 1 := by
  classical
  let η : J ⊕ J → G →* ℂ := Sum.elim χ (fun j => reflectChar (χ j))
  have hη (j : J ⊕ J) : η j ≠ 1 := by
    cases j with
    | inl j => exact hχ j
    | inr j =>
      intro h
      apply hχ j
      rw [← reflectChar_reflectChar (χ j), show reflectChar (χ j) = 1 from h]
      ext g
      simp [reflectChar_apply]
  have hu : ∀ j, ∃ u : G, η j u ≠ 1 := by
    intro j
    by_contra h
    apply hη j
    ext u
    simpa only [MonoidHom.one_apply] using not_not.mp (not_exists.mp h u)
  choose u hu using hu
  let Ψ := prependTrivial ψ
  have hΨ := prependTrivial_unitary hψ
  have hiΨ := prependTrivial_injective hinj hnone
  have h0 : Ψ 0 = 1 := rfl
  let v := filteredMeanPoint η u Ψ
  let c := filteredMeanWeight η u
  have hk (T : ℕ) (j : J) : charEval (χ j) (v T) (c T) = 0 :=
    filteredMean_kills η u Ψ T (.inl j)
  have hkr (T : ℕ) (j : J) : charEval (reflectChar (χ j)) (v T) (c T) = 0 :=
    filteredMean_kills η u Ψ T (.inr j)
  apply negIndex_sub_constant_of_null_packets hK hd v c
  · exact filteredMean_mass_one η u hu Ψ hΨ h0
  · intro g
    have he (T : ℕ) := packet_cross_eq_of_pairs K (bohrSum ψ a) χ w hrep
      (v T) (c T) (hk T) (hkr T) g
    simp_rw [he]
    exact tendsto_filteredMean_bohr_cross η u Ψ hΨ hiΨ h0 ha g
  · have he (T : ℕ) := packet_energy_eq_of_pairs K (bohrSum ψ a) χ w hrep
      (v T) (c T) (hk T)
    simp_rw [he]
    exact tendsto_filteredMean_bohr_energy η u Ψ hΨ hiΨ h0 ha

end SpectralIndex


section ZetaConstantIndex

open Zeta23
open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx rightZeros zetaZeroConfig_im_ne_zero')
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open GaloisForLFunctions.RenormalizedIntersectionTheory
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

/-- On every subgroup with dense logarithms, a negative constant adds one Weil square. -/
theorem negIndex_ratCorr_sub_constant_of_dense_log (H : Subgroup posUnits)
    (hdense : ∀ (t : ℝ) {ε : ℝ}, 0 < ε → ∃ u : H, |logPos (u : posUnits) - t| < ε)
    {d : ℝ} (hd : 0 < d) :
    negIndex (fun u : H => ratCorr u - (d : ℂ)) = negIndex ratCorr + 1 := by
  classical
  let K : H → ℂ := ratCorr ∘ H.subtype
  have hpolar : polarIndex K = negIndex ratCorr := polarIndex_ratCorr_of_dense_log H hdense
  by_cases hfinite : negIndex ratCorr = ⊤
  · have hle := polarIndex_le_negIndex (fun u : H => K u - (d : ℂ))
    rw [polarIndex_sub_constant, hpolar, hfinite] at hle
    rw [hfinite, top_add]
    exact top_le_iff.mp hle
  -- Finite index means finitely many off-critical character pairs.
  have hR : (rightZeros zetaZeroConfig).Finite := by
    by_contra hinf
    apply hfinite
    rw [negIndex_ratCorr, negIndex_zetaKernel, Set.Infinite.encard_eq hinf]
  let φ := posUnitsToHecke.comp H.subtype
  let ell := heckeLogScale.comp φ
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : H, 0 < scale ell u ∧ scale ell u < ε := by
    intro ε hε
    obtain ⟨u, hu⟩ := hdense (ε / 2) (half_pos hε)
    refine ⟨u, ?_, ?_⟩
    · change 0 < logPos (u : posUnits)
      have := (abs_lt.mp hu).1
      linarith only [this]
    · change logPos (u : posUnits) < ε
      have := (abs_lt.mp hu).2
      linarith only [this]
  have hlog := logChar_injective_of_small ell hsmall
  have hz : logChar ell 0 = 1 := by
    ext u
    simp only [logChar_apply, zero_mul, Complex.exp_zero, MonoidHom.one_apply]
  obtain ⟨e⟩ := exists_enum_onLine
  let ψ : ℕ → H →* ℂ := fun j => (onLineChar e j).comp φ
  have hψ (j : ℕ) : IsUnitaryChar (ψ j) := fun u => isUnitaryChar_onLineChar e j (φ u)
  have hiψ : Function.Injective ψ := by
    intro i j hij
    have he : (((-((e i : ℂ).im) : ℝ) : ℂ) * I) =
        (((-((e j : ℂ).im) : ℝ) : ℂ) * I) := hlog hij
    apply e.injective
    apply Subtype.ext
    apply Complex.ext
    · rw [(e i).2.2, (e j).2.2]
    · have him := congrArg Complex.im he
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, neg_inj] using him
  -- No critical zero contributes a constant spectral atom.
  have hnψ (j : ℕ) : ψ j ≠ 1 := by
    intro h
    have he : logChar ell (((-((e j : ℂ).im) : ℝ) : ℂ) * I) = logChar ell 0 := h.trans hz.symm
    have him := congrArg Complex.im (hlog he)
    apply zetaZeroConfig_im_ne_zero' _ (e j).2.1
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, Complex.zero_im, neg_eq_zero] using him
  let J := ↥hR.toFinset
  let χ : J → H →* ℂ := fun j => (zeroChar (conj (j : ℂ))).comp φ
  let w : J → ℂ := fun j => conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) j)
  have hχ (j : J) : χ j ≠ 1 := by
    intro h
    have he : logChar ell (conj (j : ℂ) - 1 / 2) = logChar ell 0 := h.trans hz.symm
    have hre := congrArg Complex.re (hlog he)
    have hj : 1 / 2 < (j : ℂ).re := (hR.mem_toFinset.mp j.2).2
    norm_num [Complex.sub_re, Complex.conj_re] at hre
    linarith only [hre, hj]
  have hrep (u : H) : K u = bohrSum ψ (onLineWeight e) u +
      ∑ j : J, pairKernel (χ j) (w j) u := by
    change ratCorr (u : posUnits) = _
    rw [ratCorr_eq_zetaKernel, zetaKernel,
      orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hR]
    change orbitKernel zetaOnLine cubicSpline (φ u) + _ = _
    rw [orbitKernel_onLine_eq_bohrSum e]
    congr 1
    rw [← Finset.sum_attach]
    have hat : hR.toFinset.attach = Finset.univ := by ext j; simp
    rw [hat]
    apply Finset.sum_congr rfl
    intro j _
    simp only [pairKernel, χ, w, MonoidHom.comp_apply, reflectChar_apply, map_inv]
    rfl
  have hindex := negIndex_sub_constant_of_spectral_decomposition
    (isHermKernel_ratCorr.comp H.subtype) ψ hψ hiψ hnψ (summable_onLineWeight e) χ hχ w hrep hd
  change negIndex (fun u : H => K u - (d : ℂ)) = polarIndex K + 1 at hindex
  rw [hpolar] at hindex
  exact hindex

end ZetaConstantIndex


section BoundedAffine

open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality

variable (p : ℕ) [Fact p.Prime]

private theorem weilPadicState_unit_slopes (c : ℝ) (g h : AffineGroupQ)
    (hg : Rat.AbsoluteValue.padic p ((slopeAbs g : ℚˣ) : ℚ) = 1)
    (hh : Rat.AbsoluteValue.padic p ((slopeAbs h : ℚˣ) : ℚ) = 1) :
    weilPadicState p c (g⁻¹ * h) = ratCorr ((slopeAbs g)⁻¹ * slopeAbs h) -
      (c : ℂ) * (Rat.AbsoluteValue.padic p (affShift h - affShift g) : ℂ) := by
  rw [weilPadicState, glueAt, conformalInduction_inv_mul
    (isConformal_negUltra (Rat.AbsoluteValue.padic p) c)]
  simp only [map_mul, map_inv, slopePow_eq_place, hg, hh, Real.one_rpow,
    one_mul, inv_one, Complex.ofReal_one, negUltra]
  change _ + (c : ℂ) * -((Rat.AbsoluteValue.padic p (affShift h - affShift g) : ℝ) : ℂ) = _
  ring

/-- Equal half-weights at shifts zero and one subtract the constant `c/2`. -/
private theorem two_translation_index_lower (H : Subgroup posUnits)
    (hunit : ∀ u : H, Rat.AbsoluteValue.padic p (((u : posUnits) : ℚˣ) : ℚ) = 1)
    (A : Subgroup AffineGroupQ)
    (hdil : ∀ u : H, dilation ((u : posUnits) : ℚˣ) ∈ A)
    (ht : translation 1 ∈ A) (c : ℝ) :
    negIndex (fun u : H => ratCorr u - ((c / 2 : ℝ) : ℂ)) ≤
      negIndex (weilPadicState p c ∘ A.subtype) := by
  classical
  let f (u : H) (k : Fin 2) : AffineGroupQ :=
    if k = 0 then dilation ((u : posUnits) : ℚˣ)
    else translation 1 * dilation ((u : posUnits) : ℚˣ)
  have hf (u : H) (k : Fin 2) : f u k ∈ A := by
    dsimp [f]
    split_ifs
    · exact hdil u
    · exact A.mul_mem ht (hdil u)
  have hs (u : H) (k : Fin 2) : slopeAbs (f u k) = (u : posUnits) := by
    dsimp [f]
    split_ifs <;> simp only [map_mul, slopeAbs_translation, slopeAbs_dilation, one_mul]
  have hb (u : H) (k : Fin 2) : affShift (f u k) = ![0, 1] k := by
    fin_cases k <;> simp [f, affShift_mul, affSlope_translation, affShift_dilation,
      affShift_translation]
  refine negIndex_le_iff.mpr fun m u => ?_
  let g : Fin m × Fin 2 → A := fun ik => ⟨f (u ik.1) ik.2, hf _ _⟩
  let w : Fin 2 → ℂ := fun _ => 1 / 2
  have hentry (i j : Fin m) (a b : Fin 2) :
      (weilPadicState p c ∘ A.subtype) ((g (i,a))⁻¹ * g (j,b)) =
        ratCorr ((u i : posUnits)⁻¹ * (u j : posUnits)) -
          (c : ℂ) * (Rat.AbsoluteValue.padic p (![0, 1] b - ![0, 1] a) : ℂ) := by
    change weilPadicState p c ((f (u i) a)⁻¹ * f (u j) b) = _
    rw [weilPadicState_unit_slopes p c _ _ (by rw [hs]; exact hunit _)
      (by rw [hs]; exact hunit _), hs, hs, hb, hb]
  have he : weightedKernelGram (weilPadicState p c ∘ A.subtype) g w =
      gram (fun u : H => ratCorr u - ((c / 2 : ℝ) : ℂ)) u := by
    ext i j
    rw [weightedKernelGram_apply]
    simp only [w, hentry]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sub_self, sub_zero, zero_sub, map_zero, map_one,
      map_neg_eq_map, Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one]
    change _ = ratCorr ((u i : posUnits)⁻¹ * (u j : posUnits)) - ((c / 2 : ℝ) : ℂ)
    simp only [map_div₀, map_one, map_ofNat]
    push_cast
    ring
  have h := hermNegIndex_weightedKernelGram_le (weilPadicState p c ∘ A.subtype) g w
  rw [he] at h
  exact h

end BoundedAffine


section TwoPrimeAffine

open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality

/-- The rational localization `ℤ[1/(qr)]`. -/
def twoPrimeRing (q r : Nat.Primes) : Subring ℚ := threePrimeRing q q r

/-- Principal-unit slopes from two primes, with translations in their localization. -/
def twoPrimePrincipalAffine (p q r : Nat.Primes) (n : ℕ) : Subgroup AffineGroupQ :=
  affineOver (twoPrimeRing q r) (twoPrimePrincipalUnits p q r n)
    (fun u => (twoPrimeUnits_mem_ring q q r u.2.1).1)

/-- Every translation in the two-prime ring is p-adically bounded when `p` is different. -/
theorem padic_le_one_twoPrimeRing (p q r : Nat.Primes) (hpq : p ≠ q) (hpr : p ≠ r)
    {b : ℚ} (hb : b ∈ twoPrimeRing q r) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    Rat.AbsoluteValue.padic p b ≤ 1 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  letI : Fact (r : ℕ).Prime := ⟨r.2⟩
  let v := Rat.AbsoluteValue.padic (p : ℕ)
  let S : Subring ℚ := {
    carrier := {x | v x ≤ 1}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := fun ha hb => (isUltra_padic p _ _).trans (max_le ha hb)
    neg_mem' := fun ha => by simpa only [Set.mem_setOf_eq, map_neg_eq_map] using ha
    mul_mem' := fun {a b} ha hb => by
      change v (a * b) ≤ 1
      rw [map_mul]
      exact (mul_le_mul ha hb (v.nonneg b) zero_le_one).trans (by norm_num) }
  have hq : v (q : ℚ)⁻¹ = 1 := by
    rw [map_inv₀, Rat.AbsoluteValue.padic_eq_padicNorm,
      padicNorm.padicNorm_of_prime_of_ne (show (p : ℕ) ≠ (q : ℕ) from
        fun h => hpq (Subtype.ext h)), Rat.cast_one, inv_one]
  have hr : v (r : ℚ)⁻¹ = 1 := by
    rw [map_inv₀, Rat.AbsoluteValue.padic_eq_padicNorm,
      padicNorm.padicNorm_of_prime_of_ne (show (p : ℕ) ≠ (r : ℕ) from
        fun h => hpr (Subtype.ext h)), Rat.cast_one, inv_one]
  have hle : twoPrimeRing q r ≤ S := by
    apply Subring.closure_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hq.le
    · exact hq.le
    · exact hr.le
  exact hle hb

/-- The entire affine subgroup has bounded p-adic translations. -/
theorem twoPrimePrincipalAffine_shift_le_one (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (n : ℕ) (g : twoPrimePrincipalAffine p q r n) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    Rat.AbsoluteValue.padic p (affShift g) ≤ 1 :=
  padic_le_one_twoPrimeRing p q r hpq hpr g.2.2.2

/-- Bounded translations already supply the native state's full successor square. -/
theorem negIndex_weilPadicState_twoPrimePrincipalAffine (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    negIndex (weilPadicState p c ∘ (twoPrimePrincipalAffine p q r n).subtype) =
      negIndex ratCorr + 1 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  let H := twoPrimePrincipalUnits p q r n
  let A := twoPrimePrincipalAffine p q r n
  have hdil (u : H) : dilation ((u : posUnits) : ℚˣ) ∈ A := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 < affSlope (dilation ((u : posUnits) : ℚˣ))
      rw [affSlope_dilation]
      exact (u : posUnits).2
    · rw [slopeAbs_dilation]
      exact u.2
    · rw [affShift_dilation]
      exact (twoPrimeRing q r).zero_mem
  have ht : translation 1 ∈ A := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 < affSlope (translation 1)
      rw [affSlope_translation]
      exact zero_lt_one
    · rw [slopeAbs_translation]
      exact H.one_mem
    · rw [affShift_translation]
      exact (twoPrimeRing q r).one_mem
  refine le_antisymm ?_ ?_
  · exact (negIndex_comp_le (weilPadicState p c) A.subtype).trans
      (by rw [negIndex_weilPadicState_eq p hc, negIndex_ratCorr])
  · rw [← negIndex_ratCorr_sub_constant_of_dense_log H
      (exists_twoPrimePrincipalUnit_log_near p q r hpq hpr hqr n) (half_pos hc)]
    exact two_translation_index_lower p H (fun u => u.2.2.1) A hdil ht c

end TwoPrimeAffine


#print axioms negIndex_ratCorr_sub_constant_of_dense_log
#print axioms padic_le_one_twoPrimeRing
#print axioms twoPrimePrincipalAffine_shift_le_one
#print axioms negIndex_weilPadicState_twoPrimePrincipalAffine

end GaloisForLFunctions.AdelicKreinGeometry
