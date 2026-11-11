import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ShiftedBoundedPacketIndexFitsTheAperture
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustIndexOfTheFiniteComb

/-!
# Physical mass Grams of bounded packets

Pairwise integrable products suffice to polarize physical mass and to
evaluate its finite complex Gram. Subtracting this Gram from the full
Weil Gram implements the same energy shift on both real components.
-/

noncomputable section

open MeasureTheory Matrix Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry HodgeTheoryOfAFixedPart

variable {ι : Type*} [Fintype ι]

/-- The physical mass matrix of a finite real packet family. -/
def packetMassGram (f : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((∫ u, f i u * f j u : ℝ) : ℂ)

theorem packetAutocorr_sum_zero (f : ι → ℝ → ℝ)
    (hf : ∀ i j, Integrable (fun u => f i u * f j u)) (c : ι → ℝ) :
    packetAutocorr (fun u => ∑ i, c i * f i u) 0 =
      ∑ i, ∑ j, c i * c j * ∫ u, f i u * f j u := by
  have hp (u : ℝ) : (∑ i, c i * f i u) * (∑ j, c j * f j u) =
      ∑ i, ∑ j, (c i * c j) * (f i u * f j u) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : ι) : Integrable (fun u => (c i * c j) * (f i u * f j u)) :=
    (hf i j).const_mul _
  simp only [packetAutocorr, add_zero, hp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

/-- The complex mass Gram is the sum of the squared masses of both real
components of a finite combination. -/
theorem hermQuad_packetMassGram (f : ι → ℝ → ℝ)
    (hf : ∀ i j, Integrable (fun u => f i u * f j u)) (c : ι → ℂ) :
    hermQuad (packetMassGram f) c =
      packetAutocorr (fun u => ∑ i, (c i).re * f i u) 0 +
        packetAutocorr (fun u => ∑ i, (c i).im * f i u) 0 := by
  rw [packetAutocorr_sum_zero f hf, packetAutocorr_sum_zero f hf]
  simp only [packetMassGram, hermQuad, dotProduct, mulVec, Finset.mul_sum,
    Complex.re_sum, Pi.star_apply, RCLike.star_def, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem packetMassPair_eq_integral {f g : ℝ → ℝ}
    (hff : Integrable (fun u => f u * f u))
    (hgg : Integrable (fun u => g u * g u))
    (hfg : Integrable (fun u => f u * g u)) :
    packetMassPair f g = ∫ u, f u * g u := by
  have hplus : Integrable (fun u => (f u + g u) * (f u + g u)) := by
    convert hff.add ((hfg.const_mul 2).add hgg) using 1
    ext u
    ring
  have hminus : Integrable (fun u => (f u - g u) * (f u - g u)) := by
    convert (hff.sub (hfg.const_mul 2)).add hgg using 1
    ext u
    ring
  have he : (fun u => (f u + g u) * (f u + g u) -
      (f u - g u) * (f u - g u)) = fun u => 4 * (f u * g u) := by
    funext u
    ring
  simp only [packetMassPair, packetAutocorr, add_zero, Pi.add_apply, Pi.sub_apply]
  rw [← integral_sub hplus hminus, he, integral_const_mul]
  ring

theorem shiftedPacketGram_eq_sub_massGram (Q : ℕ) (E : ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i j, Integrable (fun u => f i u * f j u)) :
    shiftedPacketGram Q E f = packetFormGram Q f - (E : ℂ) • packetMassGram f := by
  ext i j
  have hm := packetMassPair_eq_integral (hf i i) (hf j j) (hf i j)
  change (packetAutocorr (f i + f j) 0 - packetAutocorr (f i - f j) 0) / 4 = _ at hm
  simp only [shiftedPacketGram, packetFormGram, packetMassGram,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← hm]
  congr 1
  ring

/-- Mass-shifted nested-window Grams represent the exact shifted packet
form on both components of every complex coefficient vector. -/
theorem hermQuad_shiftedPacketGram_nested {n Q x₀ X : ℕ}
    (hx₀ : 1 ≤ x₀) (E : ℝ) (x : Fin n → ℕ)
    (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X) (c : Fin n → ℂ) :
    hermQuad (shiftedPacketGram Q E (fun i => flatPacket x₀ (x i))) c =
      (packetForm Q (fun u => ∑ i, (c i).re * flatPacket x₀ (x i) u) -
        E * packetAutocorr (fun u => ∑ i, (c i).re * flatPacket x₀ (x i) u) 0) +
      (packetForm Q (fun u => ∑ i, (c i).im * flatPacket x₀ (x i) u) -
        E * packetAutocorr (fun u => ∑ i, (c i).im * flatPacket x₀ (x i) u) 0) := by
  have hi : ∀ i j : Fin n, Integrable
      (fun u => flatPacket (x₀ : ℝ) (x i) u * flatPacket (x₀ : ℝ) (x j) u) := by
    intro i j
    simpa only [add_zero] using
      integrable_flatPacket_mul_flatPacket (x₀ : ℝ) (x i) x₀ (x j) 0
  rw [shiftedPacketGram_eq_sub_massGram Q E _ hi]
  have he (H K : Matrix (Fin n) (Fin n) ℂ) :
      hermQuad (H - (E : ℂ) • K) c = hermQuad H c - E * hermQuad K c := by
    simp only [hermQuad, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, hermQuad_packetFormGram_nested hx₀ x hx, hermQuad_packetMassGram _ hi]
  ring

/-- Two nested flat packets and all their real combinations have finite
archimedean jump energy. -/
theorem integrableOn_levyJump_flatPacket_pair {x₀ x y : ℕ}
    (hx₀ : 1 ≤ x₀) (hx : x₀ ≤ x) (hy : x₀ ≤ y) (c d : ℝ) :
    IntegrableOn (levyJump (fun u => c * flatPacket (x₀ : ℝ) x u +
      d * flatPacket (x₀ : ℝ) y u)) (Set.Ioi 0) := by
  have hxy : ∀ j ∈ (univ : Finset (Fin 2)), x₀ ≤ (![x, y] : Fin 2 → ℕ) j := by
    intro j _
    fin_cases j
    · exact hx
    · exact hy
  simpa [Fin.sum_univ_two] using
    integrableOn_levyJump_step hx₀ hxy (![c, d] : Fin 2 → ℝ)

/-- The exact support width, rather than an integer envelope for its
ratio, controls the shifted nested-packet index. -/
theorem hermNegIndex_shiftedPacketGram_nested_le {n Q x₀ X : ℕ}
    (hx₀ : 1 ≤ x₀) (E : ℝ) (x : Fin n → ℕ)
    (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X)
    (hQ : Real.log (X : ℝ) - Real.log x₀ < Real.log ((Q : ℝ) + 1))
    {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log (X : ℝ) - Real.log x₀ < 2 * A.1) :
    hermNegIndex (shiftedPacketGram Q E (fun i => flatPacket x₀ (x i))) ≤
      _root_.RHTower.PaperRestrictedWeil.negativeRank A E := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hs : ∀ i u, flatPacket (x₀ : ℝ) (x i) u ≠ 0 →
      Real.log x₀ ≤ u ∧ u ≤ Real.log X := by
    intro i u hne
    have hu : u ∈ Set.Ioc (Real.log x₀) (Real.log (x i)) := by
      by_contra hu
      exact hne (by simp only [flatPacket]; exact Set.indicator_of_notMem hu _)
    have hxi : (0 : ℝ) < x i := hx₀'.trans_le (by exact_mod_cast (hx i).1)
    exact ⟨hu.1.le, hu.2.trans (Real.log_le_log hxi (by exact_mod_cast (hx i).2))⟩
  apply hermNegIndex_shiftedPacketGram_le E (fun i => flatPacket x₀ (x i))
    (fun i => measurable_flatPacket _ _) (fun i u => abs_flatPacket_le _ _ _) hs hQ
  · intro i j
    simpa only [one_mul, Pi.add_apply] using
      integrableOn_levyJump_flatPacket_pair hx₀ (hx i).1 (hx j).1 1 1
  · intro i j
    simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg, Pi.sub_apply] using
      integrableOn_levyJump_flatPacket_pair hx₀ (hx i).1 (hx j).1 1 (-1)
  · exact hA

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
