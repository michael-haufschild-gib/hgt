import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Superlinear sampling sets have infinitely many shift failures

A locally finite symmetric set of reals whose counting function grows faster than linearly cannot
be almost invariant under any nonzero translation: for every `h ≠ 0` the set of sample points whose
translate by `h` is missing is infinite.

If that failure set were finite then, by symmetry, so would be the set of points whose translate by
`-h` is missing.  Outside a bounded window every sample point could therefore be stepped towards the
origin by `|h|` while staying in the set, so every sample point would be congruent modulo `|h|ℤ` to
one of the finitely many samples in that window.  A union of finitely many arithmetic progressions
has a counting function of linear growth, contradicting superlinearity.

This is the combinatorial half of the sampling-idealizer rigidity theorem: it supplies the infinite
shift-failure sets that force every nonzero-shift coefficient of a finite shift–Weyl operator to
vanish.
-/

namespace RHTower

open Set

/-- The number of samples of `S` in the symmetric window of radius `T`. -/
noncomputable def samplingCount (S : Set ℝ) (T : ℝ) : ℕ := (S ∩ Icc (-T) T).ncard

/-- A set of reals is *locally finite* when it meets every bounded symmetric window in a finite
set. -/
def LocallyFiniteSamples (S : Set ℝ) : Prop := ∀ T : ℝ, (S ∩ Icc (-T) T).Finite

/-- The counting function of `S` grows faster than every linear rate. -/
def SuperlinearSamples (S : Set ℝ) : Prop :=
  ∀ c : ℝ, ∃ T : ℝ, 1 ≤ T ∧ c * T < samplingCount S T

/-- The set of samples whose translate by `h` is missing. -/
def shiftFailure (S : Set ℝ) (h : ℝ) : Set ℝ := {γ | γ ∈ S ∧ γ + h ∉ S}

theorem backwardFailure_subset_neg_shiftFailure {S : Set ℝ} (hsym : ∀ x, x ∈ S → -x ∈ S) (h : ℝ) :
    {γ | γ ∈ S ∧ γ - h ∉ S} ⊆ Neg.neg '' shiftFailure S h := by
  rintro γ ⟨hγS, hγh⟩
  refine ⟨-γ, ⟨hsym γ hγS, ?_⟩, neg_neg γ⟩
  intro hmem
  refine hγh ?_
  have h2 := hsym _ hmem
  have hrw : -(-γ + h) = γ - h := by ring
  rwa [hrw] at h2

/-! ## The congruence structure of an almost translation-invariant sample set -/

/-- If every sample outside a bounded window can be stepped towards the origin by `h`, then every
sample is congruent modulo `h ℤ` to one inside the window. -/
theorem exists_window_congruence {S : Set ℝ} {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hstep : ∀ γ ∈ S, M < |γ| → γ - (if 0 ≤ γ then h else -h) ∈ S)
    {γ : ℝ} (hγ : γ ∈ S) :
    ∃ p ∈ S ∩ Icc (-(M + h)) (M + h), ∃ k : ℤ, γ = p + k * h := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |γ| ≤ M + h + N * h := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((|γ| - (M + h)) / h)
    refine ⟨N, ?_⟩
    have hlt := (div_lt_iff₀ hh).mp hN
    linarith
  induction N generalizing γ with
  | zero =>
      have hsmall : |γ| ≤ M + h := by simpa using hN
      obtain ⟨h1, h2⟩ := abs_le.mp hsmall
      exact ⟨γ, ⟨hγ, ⟨h1, h2⟩⟩, 0, by ring⟩
  | succ N ih =>
      by_cases hsmall : |γ| ≤ M + h
      · obtain ⟨h1, h2⟩ := abs_le.mp hsmall
        exact ⟨γ, ⟨hγ, ⟨h1, h2⟩⟩, 0, by ring⟩
      · replace hsmall : M + h < |γ| := not_le.mp hsmall
        have hbig : M < |γ| := by linarith
        have hstepmem := hstep γ hγ hbig
        have hle : |γ - (if 0 ≤ γ then h else -h)| ≤ M + h + N * h := by
          rcases le_or_gt 0 γ with hγ0 | hγ0
          · rw [if_pos hγ0]
            have habs : |γ| = γ := abs_of_nonneg hγ0
            have hpos : 0 ≤ γ - h := by rw [habs] at hsmall; linarith
            rw [abs_of_nonneg hpos]
            rw [habs] at hN
            push_cast at hN
            linarith
          · rw [if_neg (not_le.mpr hγ0)]
            have habs : |γ| = -γ := abs_of_neg hγ0
            have hneg : γ + h ≤ 0 := by rw [habs] at hsmall; linarith
            rw [sub_neg_eq_add, abs_of_nonpos hneg]
            rw [habs] at hN
            push_cast at hN
            linarith
        obtain ⟨p, hp, k, hk⟩ := ih hstepmem hle
        refine ⟨p, hp, k + (if 0 ≤ γ then 1 else -1), ?_⟩
        rcases le_or_gt 0 γ with hγ0 | hγ0
        · rw [if_pos hγ0] at hk ⊢
          push_cast
          linarith
        · rw [if_neg (not_le.mpr hγ0)] at hk ⊢
          push_cast
          linarith

/-! ## Linear counting for a union of finitely many progressions -/

/-- A sample set contained in finitely many arithmetic progressions of step `h` has a counting
function of linear growth. -/
theorem exists_linear_samplingCount_bound {S : Set ℝ} {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hlf : LocallyFiniteSamples S)
    (hcong : ∀ γ ∈ S, ∃ p ∈ S ∩ Icc (-(M + h)) (M + h), ∃ k : ℤ, γ = p + k * h) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → (samplingCount S T : ℝ) ≤ C * T := by
  classical
  have hP : (S ∩ Icc (-(M + h)) (M + h)).Finite := hlf (M + h)
  set P : Set ℝ := S ∩ Icc (-(M + h)) (M + h) with hPdef
  have hex : ∀ γ : ℝ, ∃ pk : ℝ × ℤ, γ ∈ S → (pk.1 ∈ P ∧ γ = pk.1 + (pk.2 : ℝ) * h) := by
    intro γ
    by_cases hγ : γ ∈ S
    · obtain ⟨p, hp, k, hk⟩ := hcong γ hγ
      exact ⟨(p, k), fun _ => ⟨hp, hk⟩⟩
    · exact ⟨(0, 0), fun hc => absurd hc hγ⟩
  choose F hF using hex
  refine ⟨(hP.toFinset.card : ℝ) * (2 * ((1 + M + h) / h + 1) + 1), fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set N : ℕ := ⌈(T + M + h) / h⌉₊ with hN
  have hmaps : ∀ γ ∈ (hlf T).toFinset,
      F γ ∈ (hP.toFinset ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset (ℝ × ℤ)) := by
    intro γ hγmem
    obtain ⟨hγS, hγ1, hγ2⟩ := (hlf T).mem_toFinset.mp hγmem
    obtain ⟨hp, hk⟩ := hF γ hγS
    obtain ⟨hp1, hp2⟩ := hp.2
    have hgamma : ((F γ).2 : ℝ) * h = γ - (F γ).1 := by linarith [hk]
    have hprod : |((F γ).2 : ℝ) * h| ≤ T + M + h := by
      rw [hgamma, abs_le]
      constructor <;> linarith
    have hkabs : |((F γ).2 : ℝ)| * h ≤ T + M + h := by
      rwa [abs_mul, abs_of_pos hh] at hprod
    have hkle : |((F γ).2 : ℝ)| ≤ (T + M + h) / h := by
      rw [le_div_iff₀ hh]
      exact hkabs
    have hkN : |((F γ).2 : ℝ)| ≤ (N : ℝ) := hkle.trans (Nat.le_ceil _)
    have hkint : |(F γ).2| ≤ (N : ℤ) := by
      have hcast : (((|(F γ).2| : ℤ)) : ℝ) ≤ (N : ℝ) := by
        rw [Int.cast_abs]
        exact hkN
      exact_mod_cast hcast
    obtain ⟨hkl, hkr⟩ := abs_le.mp hkint
    exact Finset.mem_product.mpr ⟨hP.mem_toFinset.mpr hp, Finset.mem_Icc.mpr ⟨hkl, hkr⟩⟩
  have hinj : Set.InjOn F ((hlf T).toFinset : Set ℝ) := by
    intro a hamem b hbmem hab
    have haS := ((hlf T).mem_toFinset.mp (by simpa using hamem)).1
    have hbS := ((hlf T).mem_toFinset.mp (by simpa using hbmem)).1
    obtain ⟨-, ha⟩ := hF a haS
    obtain ⟨-, hb⟩ := hF b hbS
    rw [ha, hb, hab]
  have hcard : (hlf T).toFinset.card
      ≤ (hP.toFinset ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset (ℝ × ℤ)).card :=
    Finset.card_le_card_of_injOn F hmaps hinj
  have hprodcard : (hP.toFinset ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset (ℝ × ℤ)).card
      = hP.toFinset.card * (2 * N + 1) := by
    rw [Finset.card_product, Int.card_Icc]
    congr 1
    omega
  have hcount : samplingCount S T = (hlf T).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (hlf T)
  have hNle : (N : ℝ) ≤ (T + M + h) / h + 1 := by
    have hceil := Nat.ceil_lt_add_one (a := (T + M + h) / h) (by positivity)
    linarith
  have hdiv : (T + M + h) / h ≤ T * ((1 + M + h) / h) := by
    rw [div_le_iff₀ hh, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hh)]
    nlinarith [hT, hM, hh.le]
  have hbound : ((2 * N + 1 : ℕ) : ℝ) ≤ (2 * ((1 + M + h) / h + 1) + 1) * T := by
    push_cast
    have hpos : (0 : ℝ) ≤ (1 + M + h) / h := by positivity
    nlinarith [hNle, hdiv, hT, hpos]
  calc (samplingCount S T : ℝ)
      = ((hlf T).toFinset.card : ℝ) := by rw [hcount]
    _ ≤ ((hP.toFinset.card * (2 * N + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans (le_of_eq hprodcard)
    _ = (hP.toFinset.card : ℝ) * ((2 * N + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (hP.toFinset.card : ℝ) * ((2 * ((1 + M + h) / h + 1) + 1) * T) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (hP.toFinset.card : ℝ) * (2 * ((1 + M + h) / h + 1) + 1) * T := by ring

/-! ## The aperiodicity theorem -/

/-- **Superlinear aperiodicity.**  A locally finite symmetric set of reals whose counting function
grows superlinearly misses infinitely many translates of every nonzero shift. -/
theorem infinite_shiftFailure_of_superlinear {S : Set ℝ}
    (hlf : LocallyFiniteSamples S) (hsym : ∀ x, x ∈ S → -x ∈ S)
    (hsuper : SuperlinearSamples S) {h : ℝ} (hh : h ≠ 0) :
    (shiftFailure S h).Infinite := by
  classical
  by_contra hcon
  rw [Set.not_infinite] at hcon
  have hfin : (shiftFailure S h).Finite := hcon
  have habs : 0 < |h| := abs_pos.mpr hh
  -- the forward failure set for the *positive* step `|h|`
  have hfinF : (shiftFailure S |h|).Finite := by
    rcases abs_cases h with ⟨hval, -⟩ | ⟨hval, -⟩
    · rw [hval]; exact hfin
    · rw [hval]
      refine Set.Finite.subset (hfin.image Neg.neg) ?_
      refine subset_trans ?_ (backwardFailure_subset_neg_shiftFailure hsym h)
      rintro γ ⟨hγS, hγ⟩
      exact ⟨hγS, by simpa [sub_eq_add_neg] using hγ⟩
  -- the backward failure set for the step `|h|`
  have hfinB : {γ | γ ∈ S ∧ γ - |h| ∉ S}.Finite :=
    Set.Finite.subset (hfinF.image Neg.neg) (backwardFailure_subset_neg_shiftFailure hsym |h|)
  have hU : (shiftFailure S |h| ∪ {γ | γ ∈ S ∧ γ - |h| ∉ S}).Finite := hfinF.union hfinB
  obtain ⟨M0, hM0⟩ := (hU.image (fun x => |x|)).bddAbove
  set M : ℝ := max 0 M0 with hM
  have hM0le : (0 : ℝ) ≤ M := le_max_left _ _
  have hMbound : ∀ γ ∈ shiftFailure S |h| ∪ {γ | γ ∈ S ∧ γ - |h| ∉ S}, |γ| ≤ M :=
    fun γ hγ => (hM0 ⟨γ, hγ, rfl⟩).trans (le_max_right _ _)
  -- outside the window every sample steps towards the origin
  have hstep : ∀ γ ∈ S, M < |γ| → γ - (if 0 ≤ γ then |h| else -|h|) ∈ S := by
    intro γ hγS hbig
    by_cases hγ0 : 0 ≤ γ
    · rw [if_pos hγ0]
      by_contra hcon
      exact absurd (hMbound γ (Or.inr ⟨hγS, hcon⟩)) (not_le.mpr hbig)
    · rw [if_neg hγ0, sub_neg_eq_add]
      by_contra hcon
      exact absurd (hMbound γ (Or.inl ⟨hγS, hcon⟩)) (not_le.mpr hbig)
  have hcong : ∀ γ ∈ S, ∃ p ∈ S ∩ Icc (-(M + |h|)) (M + |h|), ∃ k : ℤ, γ = p + k * |h| :=
    fun γ hγ => exists_window_congruence habs hM0le hstep hγ
  obtain ⟨C, hC⟩ := exists_linear_samplingCount_bound habs hM0le hlf hcong
  obtain ⟨T, hT, hTlt⟩ := hsuper C
  exact absurd (hC T hT) (not_le.mpr hTlt)

end RHTower
