import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes
import GaloisForLFunctions.CountingHolography.Sections.OneSidedBoundsForTheSquareGeneratorPrefix

/-!
# The upper capped-product prefix and the zero width

At every positive subcritical exponent the signed upper bound through
all conductor endpoints is equivalent to the corresponding strip.
-/

noncomputable section
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- One fixed sign suffices on the aggregate. The endpoint quantifier is
over all natural N, including incomplete conductor octaves. -/
theorem width_iff_cappedConductorPrefix {a : ℝ} (ha : 0<a) (ha' : a<1/2) :
    zetaZeroWidth≤a ↔ ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      cappedConductorPrefix N≤C*(N:ℝ)^(3+2*a) := by
  obtain ⟨K,hK,h⟩ := squareGeneratorPrefix_capped_products
  obtain ⟨B,hB,hb⟩ := conductorLog_subpower (mul_pos two_pos ha)
  have hh (N : ℕ) : |Real.log (squareGeneratorPrefix N:ℝ)-cappedConductorPrefix N| ≤
      (K*B)*(N:ℝ)^(3+2*a) := by
    apply (h N).trans
    rcases Nat.eq_zero_or_pos N with rfl|hn
    · simp [Real.zero_rpow (by linarith only [ha] : 3+2*a≠0)]
    · have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hn
      rw [Real.rpow_add hn']
      have he : (N:ℝ)^(3:ℝ)=(N:ℝ)^3 := Real.rpow_natCast _ 3
      rw [he]
      exact (mul_le_mul_of_nonneg_left (hb hn) (by positivity : 0≤K*(N:ℝ)^3)).trans_eq (by ring)
  rw [zetaZeroWidth_le_iff_one_sided_square_prefix (e := 1) ha.le ha' (by norm_num)]
  simp only [one_mul]
  constructor <;> rintro ⟨C,hC,hc⟩ <;> refine ⟨C+K*B,by positivity,fun N => ?_⟩
  · linarith only [hc N,(abs_le.mp (hh N)).1]
  · linarith only [hc N,(abs_le.mp (hh N)).2]

/-- The full positive-sign subpower prefix criterion for RH. -/
theorem riemannHypothesis_iff_cappedConductorPrefix :
    RiemannHypothesis ↔ ∀ η : ℝ, 0<η → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      cappedConductorPrefix N≤C*(N:ℝ)^(3+η) := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  constructor
  · intro hw η hη
    let a := min (η/2) (1/4)
    have ha : 0<a := lt_min (by positivity) (by norm_num)
    have ha' : a<1/2 := (min_le_right ..).trans_lt (by norm_num)
    obtain ⟨C,hC,h⟩ := (width_iff_cappedConductorPrefix ha ha').mp (hw ▸ ha.le)
    refine ⟨C,hC,fun N => (h N).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
    rcases Nat.eq_zero_or_pos N with rfl|hn
    · simp [Real.zero_rpow (by linarith only [ha] : 3+2*a≠0),
        Real.zero_rpow (by linarith only [hη] : 3+η≠0)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by linarith only [min_le_left (η/2) (1/4:ℝ)] : 3+2*a≤3+η)
  · intro h
    apply le_antisymm _ zetaZeroWidth_nonneg
    by_contra! hw
    have ha : 0<zetaZeroWidth/2 := half_pos hw
    have ha' : zetaZeroWidth/2<1/2 := by linarith only [zetaZeroWidth_le_half]
    have hs := (width_iff_cappedConductorPrefix ha ha').mpr (h _ (mul_pos two_pos ha))
    linarith only [hs,hw]

#print axioms width_iff_cappedConductorPrefix
#print axioms riemannHypothesis_iff_cappedConductorPrefix
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
