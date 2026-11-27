import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.RankBoundMonotoneInDimension
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.TwGood

/-! Complete splitting forces both the ramification index and the residue degree
to be one at each place. In particular the rational prime is a uniformizer. -/

noncomputable section

open NumberField IsDedekindDomain WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.MainNotions WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.TameKummer

variable {E : Type} [Field E] [NumberField E]

theorem ramification_inertia_of_complete_split {p : ℕ} (hp : p.Prime)
    (hs : (placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E p) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hfin := placesOver_finite_av E p hp.ne_zero
  let S := hfin.toFinset
  have hS (w : HeightOneSpectrum (𝓞 E)) : w ∈ S ↔ (p : 𝓞 E) ∈ w.asIdeal := hfin.mem_toFinset
  have hc : S.card = Module.finrank ℚ E := (Set.ncard_eq_toFinset_card _ hfin).symm.trans hs
  have hsum := sum_e_f p hp S hS
  have hle (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ S) :
      1 ≤ eWL E w * w.asIdeal.inertiaDeg ℤ := by
    letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_mem p hp w ((hS w).mp hw)
    exact Nat.mul_pos (Ideal.ramificationIdx_pos w.asIdeal ℤ) (Ideal.inertiaDeg_pos w.asIdeal ℤ)
  have hsums : (∑ w ∈ S, (1 : ℕ)) = ∑ w ∈ S, eWL E w * w.asIdeal.inertiaDeg ℤ := by
    calc
      ∑ w ∈ S, (1 : ℕ) = S.card := by simp
      _ = Module.finrank ℚ E := hc
      _ = ∑ w ∈ S, eWL E w * w.asIdeal.inertiaDeg ℤ := hsum.symm
  have h := (Finset.sum_eq_sum_iff_of_le hle).mp hsums v ((hS v).mpr hv)
  change 1 = v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ at h
  exact ⟨Nat.dvd_one.mp ⟨_, h⟩, Nat.dvd_one.mp ⟨_, h.trans (mul_comm _ _)⟩⟩

/-- At a completely split place the residue cardinality equals the rational prime,
and the prime has order exactly one. -/
theorem normV_and_notMem_sq_of_split {p : ℕ} (hp : p.Prime)
    (hs : (placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E p) :
    normV v = p ∧ (p : 𝓞 E) ∉ v.asIdeal ^ 2 := by
  obtain ⟨he, hf⟩ := ramification_inertia_of_complete_split hp hs v hv
  have hmem : (p : 𝓞 E) ∈ v.asIdeal := hv
  letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_mem p hp v hmem
  letI : (Ideal.span {(p : ℤ)}).IsMaximal := span_prime_isMaximal p hp
  have hne : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  constructor
  · have hn := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
    rw [Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal, hf, pow_one,
      Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    exact hn
  · intro hsq
    have hspan : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) =
        Ideal.span {(p : 𝓞 E)} := by simp [Ideal.map_span]
    have hspan₀ : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
      rw [hspan, Ne, Ideal.span_singleton_eq_bot]
      exact hne
    have hm := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (Ideal.span {(p : ℤ)}) v.asIdeal hspan₀
    rw [hspan, he] at hm
    have hv₁ := v.intValuation_eq_exp_neg_multiplicity hne
    rw [← hm] at hv₁
    have h := (v.intValuation_le_pow_iff_mem (p : 𝓞 E) 2).mpr hsq
    rw [hv₁, WithZero.exp_le_exp] at h
    norm_num at h

end GlobalTheory.TameKummer
