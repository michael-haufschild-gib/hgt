import GaloisForLFunctions.RHTower.SuzukiLocalCartanGermUniversality
import GaloisForLFunctions.RHTower.SuzukiMangoldtMacroscopicPrimeBlock
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeSliceEnergy
import GaloisForLFunctions.RHTower.SuzukiCanonicalSignedCompensationSaturation
import GaloisForLFunctions.HTGeometry.ReflectedPrimeHistoryReserve

/-!
# Canonical positive shared-plane Suzuki product no-go

Put every literal Suzuki center Cartan cell into one common real `SL₂` plane and multiply the
factors in increasing source-label order.  The normalized top-left entry acquires positive paths
which cross distinct source labels.  A macroscopic prime block forces this cross surplus on the
`sqrt n` scale.  Proper prime powers cost only `o(sqrt n)`, by the corpus square-root-width bound,
and Suzuki Green is also `o(sqrt n)` unconditionally.  Consequently the canonically completed
shared-plane observable tends to positive infinity along apertures `20n`.

This kills positive same-phase, natural-order shared-plane fusion as CCM-FU's missing nonlocal
producer.  It does not cover phase-twisted or indefinite shared planes, cutoff-dependent
permutations, or packet-growing signed counterterms.
-/

open scoped BigOperators
open Matrix
open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

def positiveSharedPlaneCell (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + x, Real.sqrt x; Real.sqrt x, 1]

def positiveSharedPlaneWord (xs : List ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (xs.map positiveSharedPlaneCell).prod

@[simp] theorem positiveSharedPlaneCell_zero_zero (x : ℝ) :
    positiveSharedPlaneCell x 0 0 = 1 + x := by simp [positiveSharedPlaneCell]

@[simp] theorem positiveSharedPlaneCell_one_one (x : ℝ) :
    positiveSharedPlaneCell x 1 1 = 1 := by simp [positiveSharedPlaneCell]

theorem positiveSharedPlaneCell_entry_nonneg {x : ℝ} (hx : 0 ≤ x) (i j : Fin 2) :
    0 ≤ positiveSharedPlaneCell x i j := by
  fin_cases i <;> fin_cases j <;> simp [positiveSharedPlaneCell] <;> positivity

theorem positiveSharedPlaneWord_entry_nonneg {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) (i j : Fin 2) :
    0 ≤ positiveSharedPlaneWord xs i j := by
  induction xs generalizing i j with
  | nil => simp [positiveSharedPlaneWord, Matrix.one_apply]; split_ifs <;> norm_num
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      rw [positiveSharedPlaneWord, List.map_cons, List.prod_cons]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_nonneg
        (mul_nonneg (positiveSharedPlaneCell_entry_nonneg hx i 0) (ih htail 0 j))
        (mul_nonneg (positiveSharedPlaneCell_entry_nonneg hx i 1) (ih htail 1 j))

def positiveSharedPlaneDiagProduct (xs : List ℝ) : ℝ :=
  (xs.map fun x => 1 + x).prod

theorem positiveSharedPlaneDiagProduct_nonneg {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ positiveSharedPlaneDiagProduct xs := by
  induction xs with
  | nil => simp [positiveSharedPlaneDiagProduct]
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      rw [positiveSharedPlaneDiagProduct, List.map_cons, List.prod_cons]
      exact mul_nonneg (by linarith) (ih htail)

theorem positiveSharedPlaneDiagProduct_pos {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) : 0 < positiveSharedPlaneDiagProduct xs := by
  induction xs with
  | nil => simp [positiveSharedPlaneDiagProduct]
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      change 0 < (1 + x) * positiveSharedPlaneDiagProduct xs
      exact mul_pos (by linarith) (ih htail)

theorem positiveSharedPlaneDiagProduct_le_word_zero_zero {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    positiveSharedPlaneDiagProduct xs ≤ positiveSharedPlaneWord xs 0 0 := by
  induction xs with
  | nil => simp [positiveSharedPlaneDiagProduct, positiveSharedPlaneWord]
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      change (1 + x) * positiveSharedPlaneDiagProduct xs ≤
        (positiveSharedPlaneCell x * positiveSharedPlaneWord xs) 0 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, positiveSharedPlaneCell_zero_zero]
      have hcross : 0 ≤ positiveSharedPlaneCell x 0 1 * positiveSharedPlaneWord xs 1 0 :=
        mul_nonneg (positiveSharedPlaneCell_entry_nonneg hx 0 1)
          (positiveSharedPlaneWord_entry_nonneg htail 1 0)
      exact (mul_le_mul_of_nonneg_left (ih htail) (by linarith : 0 ≤ 1 + x)).trans
        (le_add_of_nonneg_right hcross)

theorem positiveSharedPlaneWord_append_zero_zero_ge (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (hys : ∀ y ∈ ys, 0 ≤ y) :
    positiveSharedPlaneWord xs 0 0 * positiveSharedPlaneWord ys 0 0 ≤
      positiveSharedPlaneWord (xs ++ ys) 0 0 := by
  have hprod : positiveSharedPlaneWord (xs ++ ys) =
      positiveSharedPlaneWord xs * positiveSharedPlaneWord ys := by
    simp [positiveSharedPlaneWord]
  rw [hprod]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have hcross : 0 ≤ positiveSharedPlaneWord xs 0 1 * positiveSharedPlaneWord ys 1 0 :=
    mul_nonneg (positiveSharedPlaneWord_entry_nonneg hxs 0 1)
      (positiveSharedPlaneWord_entry_nonneg hys 1 0)
  linarith

theorem positiveSharedPlaneWord_filter_entry_le (p : ℝ → Bool) {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) (i j : Fin 2) :
    positiveSharedPlaneWord (xs.filter p) i j ≤ positiveSharedPlaneWord xs i j := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      by_cases hp : p x
      · simp only [List.filter_cons_of_pos hp]
        change (positiveSharedPlaneCell x * positiveSharedPlaneWord (xs.filter p)) i j ≤
          (positiveSharedPlaneCell x * positiveSharedPlaneWord xs) i j
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (ih htail 0 j)
            (positiveSharedPlaneCell_entry_nonneg hx i 0))
          (mul_le_mul_of_nonneg_left (ih htail 1 j)
            (positiveSharedPlaneCell_entry_nonneg hx i 1))
      · simp only [List.filter_cons_of_neg hp]
        change positiveSharedPlaneWord (xs.filter p) i j ≤
          (positiveSharedPlaneCell x * positiveSharedPlaneWord xs) i j
        have hleft := ih htail i j
        apply hleft.trans
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i
        · simp [positiveSharedPlaneCell]
          have h0 := positiveSharedPlaneWord_entry_nonneg htail 0 j
          have h1 := positiveSharedPlaneWord_entry_nonneg htail 1 j
          have hx0 : 0 ≤ x * positiveSharedPlaneWord xs 0 j := mul_nonneg hx h0
          have hs0 : 0 ≤ Real.sqrt x * positiveSharedPlaneWord xs 1 j :=
            mul_nonneg (Real.sqrt_nonneg x) h1
          linarith
        · simp [positiveSharedPlaneCell]
          have h0 := positiveSharedPlaneWord_entry_nonneg htail 0 j
          have h1 := positiveSharedPlaneWord_entry_nonneg htail 1 j
          have hs0 : 0 ≤ Real.sqrt x * positiveSharedPlaneWord xs 0 j :=
            mul_nonneg (Real.sqrt_nonneg x) h0
          linarith

theorem positiveSharedPlaneCell_pair_zero_zero_lower
    {delta x y : ℝ} (hdelta : 0 ≤ delta)
    (hdx : delta ≤ x) (hdy : delta ≤ y)
    (hx : x ≤ 1) (hy : y ≤ 1) :
    (1 + x) * (1 + y) * (1 + delta / 4) ≤
      (positiveSharedPlaneCell x * positiveSharedPlaneCell y) 0 0 := by
  have hx0 : 0 ≤ x := hdelta.trans hdx
  have hy0 : 0 ≤ y := hdelta.trans hdy
  have hsx := Real.sqrt_le_sqrt hdx
  have hsy := Real.sqrt_le_sqrt hdy
  have hmul : Real.sqrt delta * Real.sqrt delta ≤
      Real.sqrt x * Real.sqrt y :=
    mul_le_mul hsx hsy (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.mul_self_sqrt hdelta] at hmul
  have hdiag : (1 + x) * (1 + y) ≤ 4 := by nlinarith
  have hscaled : (1 + x) * (1 + y) * (delta / 4) ≤ delta := by
    nlinarith [mul_le_mul_of_nonneg_right hdiag hdelta]
  simp [Matrix.mul_apply, Fin.sum_univ_two, positiveSharedPlaneCell]
  nlinarith

theorem positiveSharedPlaneDiagProduct_mul_pairFactor_pow_le_word
    {delta : ℝ} (hdelta : 0 ≤ delta) {xs : List ℝ}
    (hlower : ∀ x ∈ xs, delta ≤ x) (hupper : ∀ x ∈ xs, x ≤ 1) :
    positiveSharedPlaneDiagProduct xs * (1 + delta / 4) ^ (xs.length / 2) ≤
      positiveSharedPlaneWord xs 0 0 := by
  induction xs using List.twoStepInduction with
  | nil => simp [positiveSharedPlaneDiagProduct, positiveSharedPlaneWord]
  | singleton x => simp [positiveSharedPlaneDiagProduct, positiveSharedPlaneWord]
  | cons_cons x y ys ih _ihOne =>
          have hx0 : 0 ≤ x := hdelta.trans (hlower x (by simp))
          have hy0 : 0 ≤ y := hdelta.trans (hlower y (by simp))
          have htail0 : ∀ z ∈ ys, 0 ≤ z := by
            intro z hz
            exact hdelta.trans (hlower z (by simp [hz]))
          have htailLower : ∀ z ∈ ys, delta ≤ z := by
            intro z hz
            exact hlower z (by simp [hz])
          have htailUpper : ∀ z ∈ ys, z ≤ 1 := by
            intro z hz
            exact hupper z (by simp [hz])
          have hpair := positiveSharedPlaneCell_pair_zero_zero_lower hdelta
            (hlower x (by simp)) (hlower y (by simp))
            (hupper x (by simp)) (hupper y (by simp))
          have htail := ih htailLower htailUpper
          have happend := positiveSharedPlaneWord_append_zero_zero_ge [x, y] ys
            (by
              intro z hz
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with (rfl | rfl) <;> assumption)
            htail0
          have hpair0 : 0 ≤ (positiveSharedPlaneCell x * positiveSharedPlaneCell y) 0 0 := by
            simpa [positiveSharedPlaneWord] using positiveSharedPlaneWord_entry_nonneg
              (xs := [x, y]) (by
                intro z hz
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                rcases hz with (rfl | rfl) <;> assumption) 0 0
          have hfactor0 : 0 ≤ 1 + delta / 4 := by positivity
          have hmul := mul_le_mul hpair htail
            (mul_nonneg (positiveSharedPlaneDiagProduct_nonneg htail0)
              (pow_nonneg hfactor0 (ys.length / 2))) hpair0
          have hwordPair : positiveSharedPlaneWord [x, y] =
              positiveSharedPlaneCell x * positiveSharedPlaneCell y := by simp [positiveSharedPlaneWord]
          rw [hwordPair] at happend
          calc
            positiveSharedPlaneDiagProduct (x :: y :: ys) *
                (1 + delta / 4) ^ ((x :: y :: ys).length / 2) =
              ((1 + x) * (1 + y) * (1 + delta / 4)) *
                (positiveSharedPlaneDiagProduct ys *
                  (1 + delta / 4) ^ (ys.length / 2)) := by
                    simp only [positiveSharedPlaneDiagProduct, List.map_cons, List.prod_cons,
                      List.length_cons]
                    rw [show (ys.length + 1 + 1) / 2 = ys.length / 2 + 1 by omega,
                      pow_succ]
                    ring
            _ ≤ (positiveSharedPlaneCell x * positiveSharedPlaneCell y) 0 0 *
                positiveSharedPlaneWord ys 0 0 := hmul
            _ ≤ positiveSharedPlaneWord ([x, y] ++ ys) 0 0 := happend
            _ = positiveSharedPlaneWord (x :: y :: ys) 0 0 := by rfl

def positiveSharedPlaneLogMass (xs : List ℝ) : ℝ :=
  (xs.map fun x => Real.log (1 + x)).sum

def positiveSharedPlaneCrossSurplus (xs : List ℝ) : ℝ :=
  Real.log (positiveSharedPlaneWord xs 0 0) - positiveSharedPlaneLogMass xs

theorem log_positiveSharedPlaneDiagProduct_eq_logMass {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    Real.log (positiveSharedPlaneDiagProduct xs) = positiveSharedPlaneLogMass xs := by
  induction xs with
  | nil => simp [positiveSharedPlaneDiagProduct, positiveSharedPlaneLogMass]
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      change Real.log ((1 + x) * positiveSharedPlaneDiagProduct xs) =
        Real.log (1 + x) + positiveSharedPlaneLogMass xs
      rw [Real.log_mul (by linarith) (ne_of_gt (positiveSharedPlaneDiagProduct_pos htail)), ih htail]

theorem positiveSharedPlaneCrossSurplus_nonneg {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ positiveSharedPlaneCrossSurplus xs := by
  have hdiagPos := positiveSharedPlaneDiagProduct_pos hxs
  have hwordPos : 0 < positiveSharedPlaneWord xs 0 0 :=
    hdiagPos.trans_le (positiveSharedPlaneDiagProduct_le_word_zero_zero hxs)
  have hlog := Real.log_le_log hdiagPos
    (positiveSharedPlaneDiagProduct_le_word_zero_zero hxs)
  rw [log_positiveSharedPlaneDiagProduct_eq_logMass hxs] at hlog
  exact sub_nonneg.mpr hlog

theorem positiveSharedPlaneCrossSurplus_append_ge_add (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (hys : ∀ y ∈ ys, 0 ≤ y) :
    positiveSharedPlaneCrossSurplus xs + positiveSharedPlaneCrossSurplus ys ≤
      positiveSharedPlaneCrossSurplus (xs ++ ys) := by
  have hxPos : 0 < positiveSharedPlaneWord xs 0 0 :=
    (positiveSharedPlaneDiagProduct_pos hxs).trans_le
      (positiveSharedPlaneDiagProduct_le_word_zero_zero hxs)
  have hyPos : 0 < positiveSharedPlaneWord ys 0 0 :=
    (positiveSharedPlaneDiagProduct_pos hys).trans_le
      (positiveSharedPlaneDiagProduct_le_word_zero_zero hys)
  have hxy := positiveSharedPlaneWord_append_zero_zero_ge xs ys hxs hys
  have hlog := Real.log_le_log (mul_pos hxPos hyPos) hxy
  rw [Real.log_mul (ne_of_gt hxPos) (ne_of_gt hyPos)] at hlog
  simp only [positiveSharedPlaneCrossSurplus, positiveSharedPlaneLogMass, List.map_append,
    List.sum_append]
  linarith

theorem positiveSharedPlaneCrossSurplus_middle_le (xs ys zs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (hys : ∀ y ∈ ys, 0 ≤ y)
    (hzs : ∀ z ∈ zs, 0 ≤ z) :
    positiveSharedPlaneCrossSurplus ys ≤ positiveSharedPlaneCrossSurplus (xs ++ ys ++ zs) := by
  have hxy : ∀ u ∈ xs ++ ys, 0 ≤ u := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hxs u hu
    · exact hys u hu
  have hleft := positiveSharedPlaneCrossSurplus_append_ge_add xs ys hxs hys
  have hright := positiveSharedPlaneCrossSurplus_append_ge_add (xs ++ ys) zs hxy hzs
  have hx0 := positiveSharedPlaneCrossSurplus_nonneg hxs
  have hz0 := positiveSharedPlaneCrossSurplus_nonneg hzs
  linarith

theorem positiveSharedPlaneLogMass_map_partition {α : Type*}
    (p : α → Bool) (f : α → ℝ) (as : List α) :
    positiveSharedPlaneLogMass (as.map f) =
      positiveSharedPlaneLogMass ((as.filter p).map f) +
        positiveSharedPlaneLogMass ((as.filter fun a => !p a).map f) := by
  induction as with
  | nil => simp [positiveSharedPlaneLogMass]
  | cons a as ih =>
      unfold positiveSharedPlaneLogMass at ih ⊢
      simp only [List.map_map] at ih ⊢
      by_cases ha : p a
      · simp [ha]
        rw [ih]
        ring
      · simp [ha]
        rw [ih]
        ring

theorem positiveSharedPlaneWord_map_filter_entry_le {α : Type*}
    (p : α → Bool) (f : α → ℝ) {as : List α}
    (hf : ∀ a ∈ as, 0 ≤ f a) (i j : Fin 2) :
    positiveSharedPlaneWord ((as.filter p).map f) i j ≤
      positiveSharedPlaneWord (as.map f) i j := by
  induction as generalizing i j with
  | nil => simp
  | cons a as ih =>
      have ha0 : 0 ≤ f a := hf a (by simp)
      have htail : ∀ b ∈ as, 0 ≤ f b := by
        intro b hb
        exact hf b (by simp [hb])
      by_cases ha : p a
      · simp only [List.filter_cons_of_pos ha, List.map_cons]
        change (positiveSharedPlaneCell (f a) * positiveSharedPlaneWord ((as.filter p).map f)) i j ≤
          (positiveSharedPlaneCell (f a) * positiveSharedPlaneWord (as.map f)) i j
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (ih htail 0 j)
            (positiveSharedPlaneCell_entry_nonneg ha0 i 0))
          (mul_le_mul_of_nonneg_left (ih htail 1 j)
            (positiveSharedPlaneCell_entry_nonneg ha0 i 1))
      · simp only [List.filter_cons_of_neg ha, List.map_cons]
        change positiveSharedPlaneWord ((as.filter p).map f) i j ≤
          (positiveSharedPlaneCell (f a) * positiveSharedPlaneWord (as.map f)) i j
        have hleft := ih htail i j
        apply hleft.trans
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i
        · simp [positiveSharedPlaneCell]
          have h0 := positiveSharedPlaneWord_entry_nonneg
            (xs := as.map f) (by simpa using htail) 0 j
          have h1 := positiveSharedPlaneWord_entry_nonneg
            (xs := as.map f) (by simpa using htail) 1 j
          have hfa : 0 ≤ f a * positiveSharedPlaneWord (List.map f as) 0 j :=
            mul_nonneg ha0 h0
          have hs : 0 ≤ Real.sqrt (f a) * positiveSharedPlaneWord (List.map f as) 1 j :=
            mul_nonneg (Real.sqrt_nonneg _) h1
          linarith
        · simp [positiveSharedPlaneCell]
          have h0 := positiveSharedPlaneWord_entry_nonneg
            (xs := as.map f) (by simpa using htail) 0 j
          have h1 := positiveSharedPlaneWord_entry_nonneg
            (xs := as.map f) (by simpa using htail) 1 j
          have hs : 0 ≤ Real.sqrt (f a) * positiveSharedPlaneWord (List.map f as) 0 j :=
            mul_nonneg (Real.sqrt_nonneg _) h0
          linarith

theorem positiveSharedPlaneCrossSurplus_map_ge_filter_sub_complementLogMass
    {α : Type*} (p : α → Bool) (f : α → ℝ) {as : List α}
    (hf : ∀ a ∈ as, 0 ≤ f a) :
    positiveSharedPlaneCrossSurplus ((as.filter p).map f) -
        positiveSharedPlaneLogMass ((as.filter fun a => !p a).map f) ≤
      positiveSharedPlaneCrossSurplus (as.map f) := by
  have hfull : ∀ x ∈ as.map f, 0 ≤ x := by simpa using hf
  have hprime : ∀ x ∈ (as.filter p).map f, 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hf a (List.mem_of_mem_filter ha)
  have hprimePos : 0 < positiveSharedPlaneWord ((as.filter p).map f) 0 0 :=
    (positiveSharedPlaneDiagProduct_pos hprime).trans_le
      (positiveSharedPlaneDiagProduct_le_word_zero_zero hprime)
  have hraw := positiveSharedPlaneWord_map_filter_entry_le p f hf 0 0
  have hlog := Real.log_le_log hprimePos hraw
  simp only [positiveSharedPlaneCrossSurplus]
  rw [positiveSharedPlaneLogMass_map_partition p f as]
  linarith

theorem list_sum_map_eq_toFinset_sum_of_nodup
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {as : List α} (has : as.Nodup) (f : α → M) :
    (as.map f).sum = ∑ a ∈ as.toFinset, f a := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.nodup_cons] at has
      simp [has.1, ih has.2]

theorem list_sum_map_le_sum_map {α M : Type*}
    [AddCommMonoid M] [PartialOrder M] [AddLeftMono M]
    {as : List α} {f g : α → M} (hfg : ∀ a ∈ as, f a ≤ g a) :
    (as.map f).sum ≤ (as.map g).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hfg a (by simp)) (ih fun b hb => hfg b (by simp [hb]))

theorem positiveSharedPlaneCrossSurplus_pair_lower
    {delta : ℝ} (hdelta : 0 ≤ delta) {xs : List ℝ}
    (hlower : ∀ x ∈ xs, delta ≤ x) (hupper : ∀ x ∈ xs, x ≤ 1) :
    (xs.length / 2 : ℕ) * Real.log (1 + delta / 4) ≤
      positiveSharedPlaneCrossSurplus xs := by
  have hxs : ∀ x ∈ xs, 0 ≤ x := by
    intro x hx
    exact hdelta.trans (hlower x hx)
  have hdiagPos := positiveSharedPlaneDiagProduct_pos hxs
  have hfactorPos : 0 < 1 + delta / 4 := by positivity
  have hlowerWord := positiveSharedPlaneDiagProduct_mul_pairFactor_pow_le_word
    hdelta hlower hupper
  have hprodPos : 0 < positiveSharedPlaneDiagProduct xs *
      (1 + delta / 4) ^ (xs.length / 2) :=
    mul_pos hdiagPos (pow_pos hfactorPos _)
  have hlog := Real.log_le_log hprodPos hlowerWord
  rw [Real.log_mul (ne_of_gt hdiagPos) (ne_of_gt (pow_pos hfactorPos _)),
    Real.log_pow, log_positiveSharedPlaneDiagProduct_eq_logMass hxs] at hlog
  simp only [positiveSharedPlaneCrossSurplus]
  linarith

theorem half_mul_le_log_one_add_quarter {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdelta4 : delta ≤ 4) :
    delta / 8 ≤ Real.log (1 + delta / 4) := by
  by_cases hzero : delta = 0
  · simp [hzero]
  · have hu : 0 < delta / 4 := div_pos (lt_of_le_of_ne hdelta (Ne.symm hzero)) (by norm_num)
    have hu1 : delta / 4 ≤ 1 := by linarith
    have hlog := HTGeometry.log_one_add_gt_quadratic hu
    have huSq : (delta / 4) ^ 2 ≤ delta / 4 := by nlinarith
    linarith

def suzukiPositiveSharedPlaneTwentyWindowLabelList (n : ℕ) : List ℕ :=
  (Finset.Ioc (2 * n) (5 * n)).sort (· ≤ ·)

def suzukiPositiveSharedPlaneTwentyPrimeLabelList (n : ℕ) : List ℕ :=
  (suzukiPositiveSharedPlaneTwentyWindowLabelList n).filter
    (fun k => decide k.Prime)

def suzukiPositiveSharedPlaneTwentyPrimeCellList (n : ℕ) : List ℝ :=
  (suzukiPositiveSharedPlaneTwentyPrimeLabelList n).map
    (suzukiCenterStokesCartanCell (20 * n))

def suzukiPositiveSharedPlaneTwentyPrefixLabelList (n : ℕ) : List ℕ :=
  (Finset.Icc 2 (2 * n)).sort (· ≤ ·)

def suzukiPositiveSharedPlaneTwentySuffixLabelList (n : ℕ) : List ℕ :=
  (Finset.Ioc (5 * n) (20 * n)).sort (· ≤ ·)

def suzukiPositiveSharedPlaneTwentyFullLabelList (n : ℕ) : List ℕ :=
  suzukiPositiveSharedPlaneTwentyPrefixLabelList n ++
    suzukiPositiveSharedPlaneTwentyWindowLabelList n ++
      suzukiPositiveSharedPlaneTwentySuffixLabelList n

def suzukiPositiveSharedPlaneTwentyFullCellList (n : ℕ) : List ℝ :=
  (suzukiPositiveSharedPlaneTwentyFullLabelList n).map
    (suzukiCenterStokesCartanCell (20 * n))

def suzukiPositiveSharedPlaneTwentyWindowCellList (n : ℕ) : List ℝ :=
  (suzukiPositiveSharedPlaneTwentyWindowLabelList n).map
    (suzukiCenterStokesCartanCell (20 * n))

def suzukiPositiveSharedPlaneTwentyNonprimeCellList (n : ℕ) : List ℝ :=
  ((suzukiPositiveSharedPlaneTwentyWindowLabelList n).filter
    (fun k => decide (¬ k.Prime))).map
      (suzukiCenterStokesCartanCell (20 * n))

/-- The segmented increasing list contains every natural source label from `2` through `20n`. -/
theorem suzukiPositiveSharedPlaneTwentyFullLabelList_toFinset (n : ℕ) :
    (suzukiPositiveSharedPlaneTwentyFullLabelList n).toFinset =
      Finset.Icc 2 (20 * n) := by
  ext k
  simp [suzukiPositiveSharedPlaneTwentyFullLabelList,
    suzukiPositiveSharedPlaneTwentyPrefixLabelList,
    suzukiPositiveSharedPlaneTwentyWindowLabelList,
    suzukiPositiveSharedPlaneTwentySuffixLabelList]
  omega

/-- The canonical natural-order label list has no repeated source label. -/
theorem suzukiPositiveSharedPlaneTwentyFullLabelList_nodup (n : ℕ) :
    (suzukiPositiveSharedPlaneTwentyFullLabelList n).Nodup := by
  rw [suzukiPositiveSharedPlaneTwentyFullLabelList]
  apply List.nodup_append.mpr
  constructor
  · apply List.nodup_append.mpr
    refine ⟨by simp [suzukiPositiveSharedPlaneTwentyPrefixLabelList],
      by simp [suzukiPositiveSharedPlaneTwentyWindowLabelList], ?_⟩
    intro a ha b hb
    simp [suzukiPositiveSharedPlaneTwentyPrefixLabelList] at ha
    simp [suzukiPositiveSharedPlaneTwentyWindowLabelList] at hb
    omega
  · constructor
    · simp [suzukiPositiveSharedPlaneTwentySuffixLabelList]
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · simp [suzukiPositiveSharedPlaneTwentyPrefixLabelList] at ha
        simp [suzukiPositiveSharedPlaneTwentySuffixLabelList] at hb
        omega
      · simp [suzukiPositiveSharedPlaneTwentyWindowLabelList] at ha
        simp [suzukiPositiveSharedPlaneTwentySuffixLabelList] at hb
        omega

/-- The list logarithmic mass is exactly the existing finite Suzuki Cartan log mass. -/
theorem positiveSharedPlaneLogMass_twentyFullCellList_eq (n : ℕ) :
    positiveSharedPlaneLogMass (suzukiPositiveSharedPlaneTwentyFullCellList n) =
      suzukiStokesCartanLogMass (20 * n) := by
  rw [positiveSharedPlaneLogMass, suzukiPositiveSharedPlaneTwentyFullCellList,
    suzukiStokesCartanLogMass]
  simp only [List.map_map]
  rw [list_sum_map_eq_toFinset_sum_of_nodup
    (suzukiPositiveSharedPlaneTwentyFullLabelList_nodup n)]
  rw [suzukiPositiveSharedPlaneTwentyFullLabelList_toFinset]
  simp only [Function.comp_apply]

def suzukiPositiveSharedPlaneTwentyPrimeFloor (n : ℕ) : ℝ :=
  Real.log (2 * (n : ℝ)) / (4 * Real.sqrt (20 * (n : ℝ)))

theorem suzukiCenterStokesCartanCell_twenty_mul_primeBlock_lower
    {n p : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    (hp : p ∈ _root_.RHTower.suzukiMangoldtFivePrimeBlock n) :
    suzukiPositiveSharedPlaneTwentyPrimeFloor n ≤
      suzukiCenterStokesCartanCell (20 * n) p := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ :=
    _root_.RHTower.mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hnPos : 0 < n := by
    exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hpPos : 0 < p := hpPrime.pos
  have hAPos : 0 < 20 * n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hAR : (0 : ℝ) < 20 * n := by exact_mod_cast hAPos
  have htwoNPos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hlogLower : Real.log (2 * (n : ℝ)) ≤ Real.log (p : ℝ) :=
    Real.log_le_log htwoNPos (by exact_mod_cast hpLower.le)
  have hfourP : 4 * p ≤ 20 * n := by omega
  have hfourPR : (0 : ℝ) < 4 * (p : ℝ) := by positivity
  have hlogFourP : Real.log (4 * (p : ℝ)) ≤ Real.log (20 * (n : ℝ)) :=
    Real.log_le_log hfourPR (by exact_mod_cast hfourP)
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogGap : 2 * Real.log 2 ≤
      Real.log (20 * (n : ℝ)) - Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hpR.ne', hlogFour] at hlogFourP
    linarith
  have hExpArg : -(Real.log (20 * (n : ℝ)) - Real.log (p : ℝ)) / 2 ≤
      -Real.log 2 := by linarith
  have hExp : Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (p : ℝ)) / 2) ≤
      (1 / 2 : ℝ) := by
    calc
      Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (p : ℝ)) / 2) ≤
          Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hExpArg
      _ = (1 / 2 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hFactor : (1 / 2 : ℝ) ≤
      1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (p : ℝ)) / 2) := by
    linarith
  have hlogTwoNonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
  have hsqrtPos : 0 < Real.sqrt (20 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hquot : Real.log (2 * (n : ℝ)) / Real.sqrt (20 * (n : ℝ)) ≤
      Real.log (p : ℝ) / Real.sqrt (20 * (n : ℝ)) :=
    div_le_div_of_nonneg_right hlogLower hsqrtPos.le
  have hvm : ArithmeticFunction.vonMangoldt p = Real.log p :=
    ArithmeticFunction.vonMangoldt_apply_prime hpPrime
  rw [suzukiCenterStokesCartanCell,
    _root_.RHTower.unitRieszSuzuki_prime_term hAPos hpPos, hvm]
  rw [suzukiPositiveSharedPlaneTwentyPrimeFloor]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hlogPNonneg : 0 ≤ Real.log (p : ℝ) := hlogTwoNonneg.trans hlogLower
  have hmul := mul_le_mul hquot hFactor (by positivity)
    (div_nonneg hlogPNonneg hsqrtPos.le)
  calc
    Real.log (2 * (n : ℝ)) / (4 * Real.sqrt (20 * (n : ℝ))) =
        (Real.log (2 * (n : ℝ)) / Real.sqrt (20 * (n : ℝ)) * (1 / 2)) / 2 := by ring
    _ ≤ (Real.log (p : ℝ) / Real.sqrt (20 * (n : ℝ)) *
        (1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (p : ℝ)) / 2))) / 2 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    _ = _ := by ring

theorem suzukiCenterStokesCartanCell_twenty_mul_primeBlock_le_one
    {n p : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    (hp : p ∈ _root_.RHTower.suzukiMangoldtFivePrimeBlock n) :
    suzukiCenterStokesCartanCell (20 * n) p ≤ 1 := by
  obtain ⟨_hpPrime, hpLower, hpUpper⟩ :=
    _root_.RHTower.mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hnPos : 0 < n := by
    exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hA : 2 ≤ 20 * n := by omega
  have hpIcc : p ∈ Finset.Icc 2 (20 * n) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hcell := suzukiCenterStokesCartanCell_le hA hpIcc
  have hN : Real.exp 20 ≤ 4 * (n : ℝ) := hn.trans (by nlinarith)
  have hratio := _root_.RHTower.five_mul_log_div_sqrt_le hN
  have htwenty : (5 : ℝ) * (4 * (n : ℝ)) = 20 * (n : ℝ) := by ring
  rw [htwenty] at hratio
  have hratioA : Real.log ((20 * n : ℕ) : ℝ) /
      Real.sqrt ((20 * n : ℕ) : ℝ) < 1 / 50 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
  have hhalf : Real.log ((20 * n : ℕ) : ℝ) /
      (2 * Real.sqrt ((20 * n : ℕ) : ℝ)) =
        (Real.log ((20 * n : ℕ) : ℝ) /
          Real.sqrt ((20 * n : ℕ) : ℝ)) / 2 := by ring
  rw [hhalf] at hcell
  linarith

theorem suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    0 ≤ suzukiPositiveSharedPlaneTwentyPrimeFloor n := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  rw [suzukiPositiveSharedPlaneTwentyPrimeFloor]
  exact div_nonneg (Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * n by
      have hnNat : 0 < n := by exact_mod_cast hnPos
      omega))) (by positivity)

theorem suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem
    {n k : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    (hk : k ∈ Finset.Icc 2 (20 * n)) :
    0 ≤ suzukiCenterStokesCartanCell (20 * n) k := by
  have hnPos : 0 < n := by
    exact_mod_cast (Real.exp_pos 20).trans_le hn
  exact suzukiCenterStokesCartanCell_nonneg (by omega) hk

theorem suzukiCenterStokesCartanCell_twenty_mul_le_vonMangoldt
    {n k : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    (hk : k ∈ Finset.Ioc (2 * n) (5 * n)) :
    suzukiCenterStokesCartanCell (20 * n) k ≤
      ArithmeticFunction.vonMangoldt k / (2 * Real.sqrt (20 * (n : ℝ))) := by
  have hnPos : 0 < n := by
    exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hkBounds := Finset.mem_Ioc.mp hk
  have hkPos : 0 < k := by omega
  have hAPos : 0 < 20 * n := by omega
  have hkA : k ≤ 20 * n := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkPos
  have hAR : (0 : ℝ) < 20 * (n : ℝ) := by positivity
  have hlog : Real.log (k : ℝ) ≤ Real.log (20 * (n : ℝ)) :=
    Real.log_le_log hkR (by exact_mod_cast hkA)
  have hExp : Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hFactor : 0 ≤
      1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2) := by
    linarith
  have hFactorOne :
      1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2) ≤ 1 := by
    linarith [Real.exp_pos (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2)]
  have hsqrtPos : 0 < Real.sqrt (20 * (n : ℝ)) := Real.sqrt_pos.2 hAR
  have hquot0 : 0 ≤ ArithmeticFunction.vonMangoldt k /
      Real.sqrt (20 * (n : ℝ)) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrtPos.le
  rw [suzukiCenterStokesCartanCell,
    _root_.RHTower.unitRieszSuzuki_prime_term hAPos hkPos]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hmul := mul_le_mul_of_nonneg_left hFactorOne hquot0
  have hmul' : ArithmeticFunction.vonMangoldt k / Real.sqrt (20 * (n : ℝ)) *
      (1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2)) ≤
        ArithmeticFunction.vonMangoldt k / Real.sqrt (20 * (n : ℝ)) := by
    simpa using hmul
  calc
    (ArithmeticFunction.vonMangoldt k / Real.sqrt (20 * (n : ℝ)) *
        (1 - Real.exp (-(Real.log (20 * (n : ℝ)) - Real.log (k : ℝ)) / 2))) / 2 ≤
      (ArithmeticFunction.vonMangoldt k / Real.sqrt (20 * (n : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hmul' (by norm_num)
    _ = ArithmeticFunction.vonMangoldt k / (2 * Real.sqrt (20 * (n : ℝ))) := by ring

theorem suzukiPositiveSharedPlaneTwentyFullCrossSurplus_ge_window
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyWindowCellList n) ≤
      positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyFullCellList n) := by
  let f := suzukiCenterStokesCartanCell (20 * n)
  have hprefix : ∀ x ∈ (suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map f,
      0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [suzukiPositiveSharedPlaneTwentyPrefixLabelList] at hk ⊢
    constructor
    · exact hk.1
    · omega
  have hwindow : ∀ x ∈ (suzukiPositiveSharedPlaneTwentyWindowLabelList n).map f,
      0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [suzukiPositiveSharedPlaneTwentyWindowLabelList] at hk ⊢
    omega
  have hsuffix : ∀ x ∈ (suzukiPositiveSharedPlaneTwentySuffixLabelList n).map f,
      0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [suzukiPositiveSharedPlaneTwentySuffixLabelList] at hk ⊢
    omega
  have hmiddle := positiveSharedPlaneCrossSurplus_middle_le
    ((suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map f)
    ((suzukiPositiveSharedPlaneTwentyWindowLabelList n).map f)
    ((suzukiPositiveSharedPlaneTwentySuffixLabelList n).map f)
    hprefix hwindow hsuffix
  simpa [suzukiPositiveSharedPlaneTwentyFullCellList,
    suzukiPositiveSharedPlaneTwentyFullLabelList,
    suzukiPositiveSharedPlaneTwentyWindowCellList, List.map_append, f] using hmiddle

theorem suzukiPositiveSharedPlaneTwentyWindowCrossSurplus_ge_prime_sub_nonprime
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyPrimeCellList n) -
        positiveSharedPlaneLogMass (suzukiPositiveSharedPlaneTwentyNonprimeCellList n) ≤
      positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyWindowCellList n) := by
  let labels := suzukiPositiveSharedPlaneTwentyWindowLabelList n
  let f := suzukiCenterStokesCartanCell (20 * n)
  have hf : ∀ k ∈ labels, 0 ≤ f k := by
    intro k hk
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [labels, suzukiPositiveSharedPlaneTwentyWindowLabelList] at hk ⊢
    omega
  have h := positiveSharedPlaneCrossSurplus_map_ge_filter_sub_complementLogMass
    (fun k : ℕ => decide k.Prime) f hf
  simpa [labels, f, suzukiPositiveSharedPlaneTwentyPrimeCellList,
    suzukiPositiveSharedPlaneTwentyPrimeLabelList,
    suzukiPositiveSharedPlaneTwentyNonprimeCellList,
    suzukiPositiveSharedPlaneTwentyWindowCellList] using h

def suzukiPositiveSharedPlaneTwentyPrimePowerLoss (n : ℕ) : ℝ :=
  (1 / (2 * Real.sqrt (20 * (n : ℝ)))) *
    ((Real.log (5 * n) / Real.log 2) *
      (Real.sqrt (((5 * n : ℕ) : ℝ) - (2 * n : ℕ)) + 1) *
        Real.log (5 * n))

theorem suzukiPositiveSharedPlaneTwentyNonprimeLogMass_le
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    positiveSharedPlaneLogMass (suzukiPositiveSharedPlaneTwentyNonprimeCellList n) ≤
      suzukiPositiveSharedPlaneTwentyPrimePowerLoss n := by
  let labels := (suzukiPositiveSharedPlaneTwentyWindowLabelList n).filter
    (fun k => decide (¬ k.Prime))
  let f := suzukiCenterStokesCartanCell (20 * n)
  let g := fun k : ℕ => ArithmeticFunction.vonMangoldt k /
    (2 * Real.sqrt (20 * (n : ℝ)))
  have hnPos : 0 < n := by
    exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hterm : ∀ k ∈ labels, Real.log (1 + f k) ≤ g k := by
    intro k hk
    have hkWindow : k ∈ Finset.Ioc (2 * n) (5 * n) := by
      simp [labels, suzukiPositiveSharedPlaneTwentyWindowLabelList] at hk
      exact Finset.mem_Ioc.mpr hk.1
    have hcell0 := suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
      (show k ∈ Finset.Icc 2 (20 * n) by
        simp only [Finset.mem_Icc]
        have hkb := Finset.mem_Ioc.mp hkWindow
        constructor <;> omega)
    have hlog := Real.log_le_sub_one_of_pos
      (show 0 < 1 + f k by linarith)
    have hcell := suzukiCenterStokesCartanCell_twenty_mul_le_vonMangoldt hn hkWindow
    dsimp [f, g] at hlog hcell ⊢
    linarith
  have hlist := list_sum_map_le_sum_map hterm
  have hnd : labels.Nodup := by
    have hbase : (suzukiPositiveSharedPlaneTwentyWindowLabelList n).Nodup := by
      simp [suzukiPositiveSharedPlaneTwentyWindowLabelList]
    exact hbase.filter _
  have hsum := list_sum_map_eq_toFinset_sum_of_nodup hnd g
  have hfinset : labels.toFinset =
      (Finset.Ioc (2 * n) (5 * n)).filter (fun k => ¬ k.Prime) := by
    ext k
    simp [labels, suzukiPositiveSharedPlaneTwentyWindowLabelList]
  rw [hsum, hfinset] at hlist
  have hvm := _root_.RHTower.Sieve.sum_nonprime_vonMangoldt_Ioc_le_localPrimePower
    (A := 2 * n) (B := 5 * n) (by omega) (by omega) (by omega)
  have hfactor0 : 0 ≤ 1 / (2 * Real.sqrt (20 * (n : ℝ))) := by positivity
  calc
    positiveSharedPlaneLogMass (suzukiPositiveSharedPlaneTwentyNonprimeCellList n) =
        (labels.map (fun k => Real.log (1 + f k))).sum := by
      simp [positiveSharedPlaneLogMass, suzukiPositiveSharedPlaneTwentyNonprimeCellList,
        labels, f, Function.comp_def]
    _ ≤ (labels.map g).sum := list_sum_map_le_sum_map hterm
    _ = ∑ k ∈ (Finset.Ioc (2 * n) (5 * n)).filter (fun k => ¬ k.Prime), g k := by
      rw [hsum, hfinset]
    _ = (1 / (2 * Real.sqrt (20 * (n : ℝ)))) *
        ∑ k ∈ (Finset.Ioc (2 * n) (5 * n)).filter (fun k => ¬ k.Prime),
          ArithmeticFunction.vonMangoldt k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [g]
      ring
    _ ≤ suzukiPositiveSharedPlaneTwentyPrimePowerLoss n := by
      rw [suzukiPositiveSharedPlaneTwentyPrimePowerLoss]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (mul_le_mul_of_nonneg_left hvm hfactor0)

theorem suzukiPositiveSharedPlaneTwentyPrimePowerLoss_nonneg (n : ℕ) :
    0 ≤ suzukiPositiveSharedPlaneTwentyPrimePowerLoss n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [suzukiPositiveSharedPlaneTwentyPrimePowerLoss]
  · rw [suzukiPositiveSharedPlaneTwentyPrimePowerLoss]
    have hlog5 : 0 ≤ Real.log (5 * (n : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 5 * n by omega))
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity

theorem suzukiPositiveSharedPlaneTwentyPrimePowerLoss_le_logSq
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
      Real.log (5 * (n : ℝ)) ^ 2 / Real.log 2 := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hs20 : 0 < Real.sqrt (20 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hroot : Real.sqrt (((5 * n : ℕ) : ℝ) - (2 * n : ℕ)) ≤
      Real.sqrt (20 * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hone : (1 : ℝ) ≤ Real.sqrt (20 * (n : ℝ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by
        have : 0 < n := by exact_mod_cast hnPos
        omega)
      nlinarith)
  have hscale : (1 / (2 * Real.sqrt (20 * (n : ℝ)))) *
      (Real.sqrt (((5 * n : ℕ) : ℝ) - (2 * n : ℕ)) + 1) ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hlog5 : 0 ≤ Real.log (5 * (n : ℝ)) :=
    Real.log_nonneg (by
      have hnNat : 0 < n := by exact_mod_cast hnPos
      exact_mod_cast (show 1 ≤ 5 * n by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [suzukiPositiveSharedPlaneTwentyPrimePowerLoss]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hmul := mul_le_mul_of_nonneg_right hscale
    (mul_nonneg (div_nonneg hlog5 hlog2.le) hlog5)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hmul
  calc
    1 / (2 * Real.sqrt (20 * (n : ℝ))) *
        (Real.log (5 * (n : ℝ)) / Real.log 2 *
          (Real.sqrt (5 * (n : ℝ) - 2 * (n : ℝ)) + 1) *
            Real.log (5 * (n : ℝ))) =
      (1 / (2 * Real.sqrt (20 * (n : ℝ))) *
        (Real.sqrt (5 * (n : ℝ) - 2 * (n : ℝ)) + 1)) *
          (Real.log (5 * (n : ℝ)) / Real.log 2 *
            Real.log (5 * (n : ℝ))) := by ring
    _ ≤ 1 * (Real.log (5 * (n : ℝ)) / Real.log 2 *
            Real.log (5 * (n : ℝ))) := hmul
    _ = Real.log (5 * (n : ℝ)) ^ 2 / Real.log 2 := by ring

theorem tendsto_log_sq_div_sqrt_nat_atTop_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 / 2 : ℝ))
      atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_pow_atTop (1 / 2) 2 (by norm_num)
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hcomp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.sqrt_eq_rpow]
  norm_num [Real.rpow_natCast]

theorem suzukiPositiveSharedPlaneTwentyPrimePowerLoss_div_sqrt_le
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    suzukiPositiveSharedPlaneTwentyPrimePowerLoss n / Real.sqrt (n : ℝ) ≤
      (4 / Real.log 2) *
        (Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ)) := by
  have hnOne : 1 ≤ n := by
    have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    have hnNat : 0 < n := by exact_mod_cast hnPos
    omega
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hloss := suzukiPositiveSharedPlaneTwentyPrimePowerLoss_le_logSq hn
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnOne)
  have hlog5 : Real.log (5 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    have hnFive : (5 : ℝ) ≤ n := by
      nlinarith [Real.add_one_le_exp (20 : ℝ)]
    have hmul : 5 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 5 * n) hmul
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hlog5Nonneg : 0 ≤ Real.log (5 * (n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 5 * n by omega))
  have hsq : Real.log (5 * (n : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by
    nlinarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hupper : suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
      (4 / Real.log 2) * Real.log (n : ℝ) ^ 2 := by
    calc
      suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
          Real.log (5 * (n : ℝ)) ^ 2 / Real.log 2 := hloss
      _ ≤ (4 * Real.log (n : ℝ) ^ 2) / Real.log 2 :=
        div_le_div_of_nonneg_right hsq hlog2.le
      _ = (4 / Real.log 2) * Real.log (n : ℝ) ^ 2 := by ring
  calc
    suzukiPositiveSharedPlaneTwentyPrimePowerLoss n / Real.sqrt (n : ℝ) ≤
        ((4 / Real.log 2) * Real.log (n : ℝ) ^ 2) /
          Real.sqrt (n : ℝ) := div_le_div_of_nonneg_right hupper hsqrt0
    _ = (4 / Real.log 2) *
        (Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ)) := by ring

theorem tendsto_suzukiPositiveSharedPlaneTwentyPrimePowerLoss_div_sqrt_zero :
    Tendsto (fun n : ℕ => suzukiPositiveSharedPlaneTwentyPrimePowerLoss n /
      Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  let u := fun n : ℕ => if Real.exp 20 ≤ (n : ℝ) then
    suzukiPositiveSharedPlaneTwentyPrimePowerLoss n / Real.sqrt (n : ℝ) else 0
  have hmajor := tendsto_log_sq_div_sqrt_nat_atTop_zero.const_mul
    (4 / Real.log 2 : ℝ)
  have hu : Tendsto u atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      dsimp [u]
      split_ifs
      · exact div_nonneg (suzukiPositiveSharedPlaneTwentyPrimePowerLoss_nonneg n)
          (Real.sqrt_nonneg _)
      · rfl
    · intro n
      dsimp [u]
      split_ifs with h
      · exact suzukiPositiveSharedPlaneTwentyPrimePowerLoss_div_sqrt_le h
      · positivity
    · simpa using hmajor
  apply hu.congr'
  filter_upwards [
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 20)]
    with n hn
  simp [u, hn]

theorem suzukiPositiveSharedPlaneTwentyPrimeFloor_le_one
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    suzukiPositiveSharedPlaneTwentyPrimeFloor n ≤ 1 := by
  have hne : _root_.RHTower.suzukiMangoldtFivePrimeBlock n ≠ ∅ := by
    intro hempty
    have hmass := _root_.RHTower.chebyshev_fivePrimeBlock_logMass_floor hn
    rw [hempty] at hmass
    simp at hmass
    have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    linarith
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact (suzukiCenterStokesCartanCell_twenty_mul_primeBlock_lower hn hp).trans
    (suzukiCenterStokesCartanCell_twenty_mul_primeBlock_le_one hn hp)

theorem suzukiPositiveSharedPlaneTwentyPrimeCellList_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    {x : ℝ} (hx : x ∈ suzukiPositiveSharedPlaneTwentyPrimeCellList n) :
    suzukiPositiveSharedPlaneTwentyPrimeFloor n ≤ x := by
  simp only [suzukiPositiveSharedPlaneTwentyPrimeCellList, List.mem_map] at hx
  obtain ⟨p, hpList, rfl⟩ := hx
  apply suzukiCenterStokesCartanCell_twenty_mul_primeBlock_lower hn
  rw [_root_.RHTower.mem_suzukiMangoldtFivePrimeBlock]
  simp [suzukiPositiveSharedPlaneTwentyPrimeLabelList,
    suzukiPositiveSharedPlaneTwentyWindowLabelList] at hpList
  exact ⟨hpList.2, hpList.1⟩

theorem suzukiPositiveSharedPlaneTwentyPrimeCellList_upper
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    {x : ℝ} (hx : x ∈ suzukiPositiveSharedPlaneTwentyPrimeCellList n) :
    x ≤ 1 := by
  simp only [suzukiPositiveSharedPlaneTwentyPrimeCellList, List.mem_map] at hx
  obtain ⟨p, hpList, rfl⟩ := hx
  apply suzukiCenterStokesCartanCell_twenty_mul_primeBlock_le_one hn
  rw [_root_.RHTower.mem_suzukiMangoldtFivePrimeBlock]
  simp [suzukiPositiveSharedPlaneTwentyPrimeLabelList,
    suzukiPositiveSharedPlaneTwentyWindowLabelList] at hpList
  exact ⟨hpList.2, hpList.1⟩

theorem suzukiPositiveSharedPlaneTwentyPrimeCellList_length (n : ℕ) :
    (suzukiPositiveSharedPlaneTwentyPrimeCellList n).length =
      (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card := by
  have hnd : (suzukiPositiveSharedPlaneTwentyPrimeLabelList n).Nodup := by
    have hbase : (suzukiPositiveSharedPlaneTwentyWindowLabelList n).Nodup := by
      simp [suzukiPositiveSharedPlaneTwentyWindowLabelList]
    exact hbase.filter _
  have hcard := List.toFinset_card_of_nodup hnd
  have hfinset : (suzukiPositiveSharedPlaneTwentyPrimeLabelList n).toFinset =
      _root_.RHTower.suzukiMangoldtFivePrimeBlock n := by
    ext p
    rw [_root_.RHTower.mem_suzukiMangoldtFivePrimeBlock]
    simp [suzukiPositiveSharedPlaneTwentyPrimeLabelList,
      suzukiPositiveSharedPlaneTwentyWindowLabelList]
    aesop
  rw [hfinset] at hcard
  simpa [suzukiPositiveSharedPlaneTwentyPrimeCellList] using hcard.symm

theorem suzukiMangoldtFivePrimeBlock_card_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    (n : ℝ) / (4 * Real.log (5 * (n : ℝ))) ≤
      (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hlogPos : 0 < Real.log (5 * (n : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) < n := lt_of_lt_of_le (by norm_num) <|
      (Real.add_one_le_exp 20).trans hn
    nlinarith)
  have hmass := _root_.RHTower.chebyshev_fivePrimeBlock_logMass_floor hn
  have hterm : ∀ p ∈ _root_.RHTower.suzukiMangoldtFivePrimeBlock n,
      Real.log (p : ℝ) ≤ Real.log (5 * (n : ℝ)) := by
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ :=
      _root_.RHTower.mem_suzukiMangoldtFivePrimeBlock.mp hp
    exact Real.log_le_log (by exact_mod_cast hpPrime.pos)
      (by exact_mod_cast hpUpper)
  have hupper := Finset.sum_le_card_nsmul
    (_root_.RHTower.suzukiMangoldtFivePrimeBlock n)
    (fun p => Real.log (p : ℝ)) (Real.log (5 * (n : ℝ))) hterm
  simp only [nsmul_eq_mul] at hupper
  rw [div_le_iff₀ (mul_pos (by norm_num) hlogPos)]
  nlinarith

theorem suzukiMangoldtFivePrimeBlock_two_le_card
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    2 ≤ (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card := by
  let m := (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hnFive : (5 : ℝ) ≤ n := by
    have := Real.add_one_le_exp (20 : ℝ)
    linarith
  have hlogPos : 0 < Real.log (5 * (n : ℝ)) := Real.log_pos (by nlinarith)
  have hratio := _root_.RHTower.five_mul_log_div_sqrt_le hn
  have hsqrtPos : 0 < Real.sqrt (5 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hlogSmall : Real.log (5 * (n : ℝ)) < Real.sqrt (5 * (n : ℝ)) / 50 := by
    rw [div_lt_iff₀ hsqrtPos] at hratio
    nlinarith [Real.sq_sqrt (show 0 ≤ 5 * (n : ℝ) by positivity)]
  have hsqrtLeN : Real.sqrt (5 * (n : ℝ)) ≤ (n : ℝ) := by
    have hsquare : 5 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hsqrt := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnPos.le] at hsqrt
    exact hsqrt
  have hfourLog : 4 * Real.log (5 * (n : ℝ)) < (n : ℝ) := by linarith
  have hcount := suzukiMangoldtFivePrimeBlock_card_lower hn
  by_contra hnot
  have hm : m ≤ 1 := by omega
  have hmR : (m : ℝ) ≤ 1 := by exact_mod_cast hm
  have hratioOne : (n : ℝ) / (4 * Real.log (5 * (n : ℝ))) ≤ 1 :=
    hcount.trans hmR
  rw [div_le_iff₀ (mul_pos (by norm_num) hlogPos)] at hratioOne
  linarith

theorem suzukiMangoldtFivePrimeBlock_card_quarter_le_div_two
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    ((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card : ℝ) / 4 ≤
      (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) := by
  have htwo := suzukiMangoldtFivePrimeBlock_two_le_card hn
  have hnat : (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card ≤
      4 * ((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2) := by omega
  have hnatR : ((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card : ℝ) ≤
      4 * (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

theorem suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_pair_floor
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) *
        (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) ≤
      positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyPrimeCellList n) := by
  have hpair := positiveSharedPlaneCrossSurplus_pair_lower
    (suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg hn)
    (xs := suzukiPositiveSharedPlaneTwentyPrimeCellList n)
    (fun x hx => suzukiPositiveSharedPlaneTwentyPrimeCellList_lower hn hx)
    (fun x hx => suzukiPositiveSharedPlaneTwentyPrimeCellList_upper hn hx)
  have hlog := half_mul_le_log_one_add_quarter
    (suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg hn)
    ((suzukiPositiveSharedPlaneTwentyPrimeFloor_le_one hn).trans (by norm_num))
  rw [suzukiPositiveSharedPlaneTwentyPrimeCellList_length] at hpair
  have hcount : (0 : ℝ) ≤
      (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog hcount]

theorem suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_sqrt_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyPrimeCellList n) := by
  let m := (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card
  let q := m / 2
  let L2 := Real.log (2 * (n : ℝ))
  let L5 := Real.log (5 * (n : ℝ))
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hnPos
  have hL2 : 0 < L2 := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * n by omega))
  have hL5 : 0 < L5 := Real.log_pos (by
    exact_mod_cast (show 1 < 5 * n by omega))
  have hm := suzukiMangoldtFivePrimeBlock_card_lower hn
  have hq := suzukiMangoldtFivePrimeBlock_card_quarter_le_div_two hn
  have hqLower : (n : ℝ) / (16 * L5) ≤ (q : ℝ) := by
    dsimp [m, q, L5] at hm hq ⊢
    calc
      (n : ℝ) / (16 * Real.log (5 * (n : ℝ))) =
          ((n : ℝ) / (4 * Real.log (5 * (n : ℝ)))) / 4 := by ring
      _ ≤ ((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card : ℝ) / 4 :=
        div_le_div_of_nonneg_right hm (by norm_num)
      _ ≤ _ := hq
  have hsquare : 5 * (n : ℝ) ≤ (2 * (n : ℝ)) ^ 2 := by
    have hnFive : (5 : ℝ) ≤ n := by
      nlinarith [Real.add_one_le_exp (20 : ℝ)]
    nlinarith
  have hlogRatioRaw : L5 ≤ 2 * L2 := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 5 * n) hsquare
    dsimp [L2, L5]
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hlogRatio : (1 / 2 : ℝ) ≤ L2 / L5 := by
    rw [le_div_iff₀ hL5]
    nlinarith
  have hdelta0 := suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg hn
  have hpair := suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_pair_floor hn
  have hprod : ((n : ℝ) / (16 * L5)) *
      (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) ≤
        positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyPrimeCellList n) := by
    apply (mul_le_mul_of_nonneg_right hqLower (div_nonneg hdelta0 (by norm_num))).trans
    simpa [q, m] using hpair
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hsqrt20 : 0 < Real.sqrt (20 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtMul : Real.sqrt (20 * (n : ℝ)) =
      Real.sqrt 20 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 20)]
  have hrewrite : ((n : ℝ) / (16 * L5)) *
      (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) =
        (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (L2 / L5) := by
    rw [suzukiPositiveSharedPlaneTwentyPrimeFloor]
    dsimp [L2]
    rw [hsqrtMul]
    field_simp [hL5.ne', hsqrtN.ne', hsqrt20.ne']
    rw [Real.sq_sqrt hnPos.le]
    ring
  have hscale0 : 0 ≤ Real.sqrt (n : ℝ) / (512 * Real.sqrt 20) := by positivity
  have hmain : Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (L2 / L5) := by
    have := mul_le_mul_of_nonneg_left hlogRatio hscale0
    calc
      Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) =
          (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (1 / 2) := by ring
      _ ≤ _ := this
  rw [hrewrite] at hprod
  exact hmain.trans hprod

theorem suzukiPositiveSharedPlaneTwentyFullCrossSurplus_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
        suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
      positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyFullCellList n) := by
  have hprime := suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_sqrt_lower hn
  have hnonprime := suzukiPositiveSharedPlaneTwentyNonprimeLogMass_le hn
  have hwindow :=
    suzukiPositiveSharedPlaneTwentyWindowCrossSurplus_ge_prime_sub_nonprime hn
  have hfull := suzukiPositiveSharedPlaneTwentyFullCrossSurplus_ge_window hn
  linarith

def suzukiPositiveSharedPlaneTwentyCompletedObservable (n : ℕ) : ℝ :=
  suzukiCompletedStokesCartanWardObservable (20 * n) +
    2 * positiveSharedPlaneCrossSurplus (suzukiPositiveSharedPlaneTwentyFullCellList n)

/-- Exact closed form: top-left log of the natural shared-plane word, forced quadratic
counterterm, and literal regular-Ward subtraction. -/
theorem suzukiPositiveSharedPlaneTwentyCompletedObservable_eq (n : ℕ) :
    suzukiPositiveSharedPlaneTwentyCompletedObservable n =
      2 * Real.log
        (positiveSharedPlaneWord (suzukiPositiveSharedPlaneTwentyFullCellList n) 0 0) +
        suzukiStokesCartanQuadraticCounterterm (20 * n) -
          suzukiUnitRieszRegularWardMass (Real.log ((20 * n : ℕ) : ℝ)) := by
  rw [suzukiPositiveSharedPlaneTwentyCompletedObservable,
    suzukiCompletedStokesCartanWardObservable,
    positiveSharedPlaneCrossSurplus,
    positiveSharedPlaneLogMass_twentyFullCellList_eq]
  ring

theorem suzukiPositiveSharedPlaneTwentyCompletedObservable_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    _root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) +
        2 * (Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
          suzukiPositiveSharedPlaneTwentyPrimePowerLoss n) ≤
      suzukiPositiveSharedPlaneTwentyCompletedObservable n := by
  have hnPos : 0 < n := by exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hA : 2 ≤ 20 * n := by omega
  have hcompleted := suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder
    (20 * n - 2)
  rw [Nat.sub_add_cancel hA] at hcompleted
  have hremainder := suzukiStokesCartanCubicRemainderMass_nonneg hA
  have hcross := suzukiPositiveSharedPlaneTwentyFullCrossSurplus_lower hn
  rw [suzukiPositiveSharedPlaneTwentyCompletedObservable, hcompleted]
  linarith

theorem tendsto_unitRieszSuzukiGreen_log_twenty_mul_div_sqrt_zero :
    Tendsto (fun n : ℕ => _root_.RHTower.unitRieszSuzukiGreen
      (Real.log ((20 * n : ℕ) : ℝ)) /
      Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have htwenty : Tendsto (fun n : ℕ => 20 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hcomp := tendsto_unitRieszSuzukiGreen_logNat_div_sqrt_atTop_zero.comp htwenty
  have hmul := hcomp.const_mul (Real.sqrt 20)
  have hmul0 : Tendsto (fun n : ℕ => Real.sqrt 20 *
      (_root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) /
        Real.sqrt ((20 * n : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hsqrt20 : 0 < Real.sqrt (20 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtMul : Real.sqrt ((20 * n : ℕ) : ℝ) =
      Real.sqrt 20 * Real.sqrt (n : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 20)]
  rw [hsqrtMul]
  field_simp [hsqrtN.ne', hsqrt20.ne']

def suzukiPositiveSharedPlaneTwentyNormalizedLower (n : ℕ) : ℝ :=
  _root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) /
      Real.sqrt (n : ℝ) +
    1 / (512 * Real.sqrt 20) -
      2 * (suzukiPositiveSharedPlaneTwentyPrimePowerLoss n / Real.sqrt (n : ℝ))

theorem tendsto_suzukiPositiveSharedPlaneTwentyNormalizedLower :
    Tendsto suzukiPositiveSharedPlaneTwentyNormalizedLower atTop
      (𝓝 (1 / (512 * Real.sqrt 20))) := by
  have hgreen := tendsto_unitRieszSuzukiGreen_log_twenty_mul_div_sqrt_zero
  have hloss := tendsto_suzukiPositiveSharedPlaneTwentyPrimePowerLoss_div_sqrt_zero
  have hconst : Tendsto (fun _ : ℕ => (1 / (512 * Real.sqrt 20) : ℝ)) atTop
      (𝓝 (1 / (512 * Real.sqrt 20))) := tendsto_const_nhds
  have hlim := (hgreen.add hconst).sub (hloss.const_mul 2)
  rw [show suzukiPositiveSharedPlaneTwentyNormalizedLower = fun n : ℕ =>
      _root_.RHTower.unitRieszSuzukiGreen (Real.log (20 * (n : ℝ))) /
          Real.sqrt (n : ℝ) +
        1 / (512 * Real.sqrt 20) -
          2 * (suzukiPositiveSharedPlaneTwentyPrimePowerLoss n / Real.sqrt (n : ℝ)) by
    funext n
    rw [suzukiPositiveSharedPlaneTwentyNormalizedLower]
    simp only [Nat.cast_mul, Nat.cast_ofNat]]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, zero_add, mul_zero, sub_zero] using hlim

theorem suzukiPositiveSharedPlaneTwentyNormalizedLower_le_observable_div_sqrt
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    suzukiPositiveSharedPlaneTwentyNormalizedLower n ≤
      suzukiPositiveSharedPlaneTwentyCompletedObservable n / Real.sqrt (n : ℝ) := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hobs := suzukiPositiveSharedPlaneTwentyCompletedObservable_lower hn
  have hdiv := div_le_div_of_nonneg_right hobs hsqrt.le
  rw [suzukiPositiveSharedPlaneTwentyNormalizedLower]
  calc
    _root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) /
        Real.sqrt (n : ℝ) +
          1 / (512 * Real.sqrt 20) -
        2 * (suzukiPositiveSharedPlaneTwentyPrimePowerLoss n /
          Real.sqrt (n : ℝ)) =
      (_root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) +
        2 * (Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
          suzukiPositiveSharedPlaneTwentyPrimePowerLoss n)) /
            Real.sqrt (n : ℝ) := by
      field_simp [hsqrt.ne']
      ring
    _ ≤ _ := hdiv

theorem tendsto_suzukiPositiveSharedPlaneTwentyCompletedObservable_atTop :
    Tendsto suzukiPositiveSharedPlaneTwentyCompletedObservable atTop atTop := by
  let c : ℝ := 1 / (512 * Real.sqrt 20)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ᶠ n : ℕ in atTop,
      c / 2 < suzukiPositiveSharedPlaneTwentyNormalizedLower n :=
    (tendsto_order.1 tendsto_suzukiPositiveSharedPlaneTwentyNormalizedLower).1
      (c / 2) (by linarith)
  rw [tendsto_atTop]
  intro B
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlower,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 20),
    hsqrtTop.eventually_ge_atTop (2 * B / c)] with n hnLower hnLarge hnSqrt
  have hnorm := suzukiPositiveSharedPlaneTwentyNormalizedLower_le_observable_div_sqrt hnLarge
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hnLarge
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hobs : (c / 2) * Real.sqrt (n : ℝ) <
      suzukiPositiveSharedPlaneTwentyCompletedObservable n := by
    have hratio : c / 2 <
        suzukiPositiveSharedPlaneTwentyCompletedObservable n / Real.sqrt (n : ℝ) :=
      hnLower.trans_le hnorm
    rwa [lt_div_iff₀ hsqrtPos] at hratio
  have hB : B ≤ (c / 2) * Real.sqrt (n : ℝ) := by
    have hcne : c ≠ 0 := hc.ne'
    calc
      B = (c / 2) * (2 * B / c) := by field_simp
      _ ≤ (c / 2) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnSqrt (by linarith)
  exact hB.trans hobs.le

/-- Closed producer-class certificate for positive same-phase natural-order shared-plane fusion. -/
def SuzukiPositiveSharedPlaneNaturalOrderedRouteKilled : Prop :=
  ¬ ∃ B : ℝ, ∀ n : ℕ,
    |suzukiPositiveSharedPlaneTwentyCompletedObservable n| ≤ B

/-- **CCM-FU route-class kill.** The literal completed observable of the canonical increasing
positive shared `SL₂` product is unbounded; in fact it tends to positive infinity along `20n`. -/
theorem no_bounded_suzukiPositiveSharedPlaneTwentyCompletedObservable :
    SuzukiPositiveSharedPlaneNaturalOrderedRouteKilled := by
  rintro ⟨B, hB⟩
  have hevent :=
    tendsto_suzukiPositiveSharedPlaneTwentyCompletedObservable_atTop.eventually_ge_atTop (B + 1)
  rcases hevent.exists with ⟨n, hn⟩
  have habs := hB n
  have hself := le_abs_self (suzukiPositiveSharedPlaneTwentyCompletedObservable n)
  linarith

end GaloisForLFunctions.RHTower
