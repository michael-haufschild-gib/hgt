import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Arbitrarily large clusters of actual critical-line donor zeros

The unconditional superlinear count of simple critical zeros forces
arbitrarily many distinct donor ordinates in fixed short intervals at
arbitrarily large heights. A uniform bound per interval would give a
linear total count by assigning ordinates to integer bins.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality

private def simpleCriticalPacket (T : ℝ) : Finset ℂ :=
  (RHTower.stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ (analyticOrderAt RHTower.xi z).toNat = 1)

private theorem mem_simpleCriticalPacket {T : ℝ} {z : ℂ} :
    z ∈ simpleCriticalPacket T ↔ z.re = 1 / 2 ∧ 0 < z.im ∧ z.im ≤ T ∧
      RHTower.xi z = 0 ∧ (analyticOrderAt RHTower.xi z).toNat = 1 := by
  rw [simpleCriticalPacket, Finset.mem_filter, RHTower.mem_stripFinsetPos]
  constructor
  · rintro ⟨⟨_, _, him, hT, hz⟩, hre, hm⟩
    exact ⟨hre, him, hT, hz, hm⟩
  · rintro ⟨hre, him, hT, hz, hm⟩
    exact ⟨⟨by rw [hre]; norm_num, by rw [hre]; norm_num, him, hT, hz⟩, hre, hm⟩

private theorem ordinate_family_of_packet {S : Finset ℂ} {n : ℕ} {H ell : ℝ}
    (hn : n ≤ S.card)
    (hS : ∀ z ∈ S, z.re = 1 / 2 ∧ RHTower.xi z = 0 ∧ H ≤ z.im ∧ z.im ≤ H + ell) :
    ∃ γ : Fin n → ℝ, Function.Injective γ ∧
      ∀ i, H ≤ γ i ∧ γ i ≤ H + ell ∧ RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0 := by
  classical
  obtain ⟨S', hsub, hcard⟩ := Finset.exists_subset_card_eq hn
  subst n
  let e := S'.equivFin.symm
  let γ := fun i : Fin S'.card => (e i).val.im
  have hmem (i : Fin S'.card) : (e i).val ∈ S := hsub (e i).property
  refine ⟨γ, ?_, fun i => ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Complex.ext
    · exact (hS _ (hmem i)).1.trans (hS _ (hmem j)).1.symm
    · exact hij
  · obtain ⟨hre, hz, hlow, hhigh⟩ := hS _ (hmem i)
    refine ⟨hlow, hhigh, ?_⟩
    have he : (e i).val = 1 / 2 + (γ i : ℂ) * I := by
      apply Complex.ext
      · simpa using hre
      · simp [γ]
    rwa [← he]

/-- Arbitrarily large critical donor clusters occur in fixed-width intervals at unbounded heights. -/
theorem exists_critical_donor_cluster (n : ℕ) {ell : ℝ} (hell : 0 < ell) (M : ℝ) :
    ∃ (H : ℝ) (γ : Fin n → ℝ), M ≤ H ∧ 1 ≤ H ∧ Function.Injective γ ∧
      ∀ i, H ≤ γ i ∧ γ i ≤ H + ell ∧ RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0 := by
  classical
  let M₀ := max M 1
  let low := simpleCriticalPacket (M₀ + ell)
  let bin := fun z : ℂ => ⌊z.im / ell⌋₊
  by_contra hnone
  have hfiber (T : ℝ) (b : ℕ) :
      (((simpleCriticalPacket T) \ low).filter (fun z => bin z = b)).card ≤ n := by
    by_contra hlarge
    let S := ((simpleCriticalPacket T) \ low).filter (fun z => bin z = b)
    have hn : n < S.card := lt_of_not_ge hlarge
    obtain ⟨z, hz⟩ := Finset.card_pos.mp ((Nat.zero_le n).trans_lt hn)
    obtain ⟨hzD, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzT, hzlow⟩ := Finset.mem_sdiff.mp hzD
    obtain ⟨hzre, hzpos, hzupper, hzxi, hzmult⟩ := mem_simpleCriticalPacket.mp hzT
    have hhigh : M₀ + ell < z.im := by
      apply lt_of_not_ge
      intro h
      exact hzlow (mem_simpleCriticalPacket.mpr ⟨hzre, hzpos, h, hzxi, hzmult⟩)
    have hbLower : M₀ < (b : ℝ) * ell := by
      have h := Nat.lt_floor_add_one (z.im / ell)
      change z.im / ell < (bin z : ℝ) + 1 at h
      rw [hzb] at h
      have h' := (div_lt_iff₀ hell).mp h
      nlinarith only [h', hhigh]
    have hS (y : ℂ) (hy : y ∈ S) : y.re = 1 / 2 ∧ RHTower.xi y = 0 ∧
        (b : ℝ) * ell ≤ y.im ∧ y.im ≤ (b : ℝ) * ell + ell := by
      obtain ⟨hyD, hyb⟩ := Finset.mem_filter.mp hy
      have hyT := (Finset.mem_sdiff.mp hyD).1
      obtain ⟨hyre, hypos, _, hyxi, _⟩ := mem_simpleCriticalPacket.mp hyT
      have hlow := Nat.floor_le (div_nonneg hypos.le hell.le)
      have hhigh := Nat.lt_floor_add_one (y.im / ell)
      change (bin y : ℝ) ≤ y.im / ell at hlow
      change y.im / ell < (bin y : ℝ) + 1 at hhigh
      rw [hyb] at hlow hhigh
      have hl := (le_div_iff₀ hell).mp hlow
      have hh := (div_lt_iff₀ hell).mp hhigh
      exact ⟨hyre, hyxi, hl, by nlinarith only [hh]⟩
    obtain ⟨γ, hγ, hγS⟩ := ordinate_family_of_packet hn.le hS
    exact hnone ⟨(b : ℝ) * ell, γ,
      (le_max_left M 1).trans hbLower.le, (le_max_right M 1).trans hbLower.le, hγ, hγS⟩
  have hlinear (T : ℝ) (hT : 1 ≤ T) :
      (RHTower.xiSimpleCriticalZeroCount T : ℝ) ≤
        ((n : ℝ) / ell + n) * (1 + T) + low.card := by
    let high := (simpleCriticalPacket T) \ low
    have himg : (high.image bin).card ≤ ⌊T / ell⌋₊ + 1 := by
      have hsub : high.image bin ⊆ Finset.range (⌊T / ell⌋₊ + 1) := by
        intro b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
        have hzT := (mem_simpleCriticalPacket.mp (Finset.mem_sdiff.mp hz).1).2.2.1
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le
          (Nat.floor_mono (div_le_div_of_nonneg_right hzT hell.le)))
      simpa only [Finset.card_range] using Finset.card_le_card hsub
    have hhigh : high.card ≤ n * (⌊T / ell⌋₊ + 1) :=
      (Finset.card_le_mul_card_image high n (fun b _ => hfiber T b)).trans
        (Nat.mul_le_mul_left n himg)
    have hsub : simpleCriticalPacket T ⊆ low ∪ high := by
      intro z hz
      by_cases hl : z ∈ low
      · exact Finset.mem_union_left _ hl
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hl⟩)
    have hc : (simpleCriticalPacket T).card ≤ low.card + n * (⌊T / ell⌋₊ + 1) :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le low high).trans
        (Nat.add_le_add_left hhigh low.card))
    have hcR : (RHTower.xiSimpleCriticalZeroCount T : ℝ) ≤
        (low.card : ℝ) + (n : ℝ) * ((⌊T / ell⌋₊ : ℝ) + 1) := by
      exact_mod_cast hc
    have hf : (⌊T / ell⌋₊ : ℝ) ≤ T / ell :=
      Nat.floor_le (div_nonneg (by linarith only [hT]) hell.le)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbound := mul_le_mul_of_nonneg_left (add_le_add_right hf 1) hn0
    have hpos : 0 ≤ (n : ℝ) / ell := div_nonneg hn0 hell.le
    have hprod : 0 ≤ (n : ℝ) * T := mul_nonneg hn0 (by linarith only [hT])
    simp only [div_eq_mul_inv] at hcR hbound hpos ⊢
    nlinarith only [hcR, hbound, hpos, hprod]
  exact RHTower.not_linear_bound_of_superlinear (by positivity : 0 < (1 : ℝ) / (72 * Real.pi))
    RHTower.eventually_superlinear_xiSimpleCriticalZeroCount hlinear

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_critical_donor_cluster
