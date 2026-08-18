import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence

/-!
# The gate-relative rate--distortion functional

Among all encoders supported on a set of admissible words, the synthesis divergence against the
local gate prior is minimised exactly by the prior conditioned on that set, and its value there is
the negative logarithm of the admissible mass.  The lower half is Gibbs' inequality applied to the
conditioned reference, which vanishes off the admissible set, so it needs the absolutely continuous
form of Gibbs rather than the strictly positive one.

Two immediate consequences bound the resulting surprisal.  The prior mass of the words of length at
least `n` is exactly `aⁿ` — the geometric length tail, obtained by splitting a long word into its
first `n` letters and the rest — so a set of long words is geometrically light; and a single
admissible witness word caps the surprisal by its own affine word cost.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Gibbs

variable {α : Type*}

/-- **Gibbs' inequality under absolute continuity.**  The reference law may vanish where the
encoder does. -/
theorem relEntropy_nonneg_of_absolutelyContinuous {q p : α → ℝ}
    (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 ≤ p w) (hac : ∀ w, 0 < q w → 0 < p w)
    (hqsum : HasSum q 1) (hpsum : HasSum p 1)
    (hs : Summable fun w => q w * Real.log (q w / p w)) :
    0 ≤ relEntropy q p := by
  have hbound : ∀ w, -(q w * Real.log (q w / p w)) ≤ p w - q w := by
    intro w
    rcases eq_or_lt_of_le (hq w) with hzero | hpos
    · rw [← hzero]
      simp
      linarith [hp w]
    · have hpw : 0 < p w := hac w hpos
      have hratio : 0 < p w / q w := div_pos hpw hpos
      have hlog := log_le_sub_one hratio
      have hneg : -(q w * Real.log (q w / p w)) = q w * Real.log (p w / q w) := by
        rw [show p w / q w = (q w / p w)⁻¹ by rw [inv_div], Real.log_inv]
        ring
      rw [hneg]
      calc q w * Real.log (p w / q w) ≤ q w * (p w / q w - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
        _ = p w - q w := by field_simp
  have hneg : Summable fun w => -(q w * Real.log (q w / p w)) := hs.neg
  have hdiff : HasSum (fun w => p w - q w) 0 := by
    have := hpsum.sub hqsum
    simpa using this
  have hle : ∑' w, -(q w * Real.log (q w / p w)) ≤ 0 := by
    calc ∑' w, -(q w * Real.log (q w / p w)) ≤ ∑' w, (p w - q w) :=
          hneg.tsum_le_tsum hbound hdiff.summable
      _ = 0 := hdiff.tsum_eq
  rw [relEntropy]
  rw [tsum_neg] at hle
  linarith

end Gibbs

section Conditioning

variable {α : Type*}

/-- The reference law conditioned on a set of admissible words. -/
def condLaw (p : α → ℝ) (G : Set α) (mass : ℝ) : α → ℝ :=
  fun w => if w ∈ G then p w / mass else 0

theorem condLaw_nonneg {p : α → ℝ} (hp : ∀ w, 0 ≤ p w) (G : Set α) {mass : ℝ}
    (hmass : 0 < mass) (w : α) : 0 ≤ condLaw p G mass w := by
  unfold condLaw
  split_ifs
  · exact div_nonneg (hp w) hmass.le
  · exact le_rfl

/-- **`(15)`.**  Relative entropy against the conditioned reference differs from relative entropy
against the reference by exactly the log mass of the conditioning set. -/
theorem relEntropy_condLaw {q p : α → ℝ} (G : Set α) {mass : ℝ} (hmass : 0 < mass)
    (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 < p w)
    (hsupp : ∀ w, w ∉ G → q w = 0) (hqsum : HasSum q 1)
    (hs : Summable fun w => q w * Real.log (q w / p w)) :
    relEntropy q (condLaw p G mass) = relEntropy q p + Real.log mass := by
  classical
  have hpoint : ∀ w, q w * Real.log (q w / condLaw p G mass w) =
      q w * Real.log (q w / p w) + q w * Real.log mass := by
    intro w
    by_cases hw : w ∈ G
    · rcases eq_or_lt_of_le (hq w) with hzero | hpos
      · rw [← hzero]; ring
      · have hpw : 0 < p w := hp w
        have hcond : condLaw p G mass w = p w / mass := by
          unfold condLaw; rw [if_pos hw]
        rw [hcond]
        have hdiv : q w / (p w / mass) = (q w / p w) * mass := by
          field_simp
        rw [hdiv, Real.log_mul (by positivity) (ne_of_gt hmass)]
        ring
    · rw [hsupp w hw]
      ring
  have hsummable2 : Summable fun w => q w * Real.log mass := by
    exact hqsum.summable.mul_right _
  unfold relEntropy
  rw [tsum_congr hpoint, hs.tsum_add hsummable2]
  congr 1
  rw [tsum_mul_right, hqsum.tsum_eq, one_mul]

/-- **`(12)`, lower half.**  Every encoder supported on the admissible set pays at least the
negative log mass of that set. -/
theorem neg_log_mass_le_relEntropy {q p : α → ℝ} (G : Set α) {mass : ℝ} (hmass : 0 < mass)
    (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 < p w)
    (hsupp : ∀ w, w ∉ G → q w = 0) (hqsum : HasSum q 1)
    (hcond : HasSum (condLaw p G mass) 1)
    (hs : Summable fun w => q w * Real.log (q w / p w))
    (hs' : Summable fun w => q w * Real.log (q w / condLaw p G mass w)) :
    -Real.log mass ≤ relEntropy q p := by
  have hnn := relEntropy_nonneg_of_absolutelyContinuous (q := q) (p := condLaw p G mass)
    hq (condLaw_nonneg (fun w => (hp w).le) G hmass) ?_ hqsum hcond hs'
  · rw [relEntropy_condLaw G hmass hq hp hsupp hqsum hs] at hnn
    linarith
  · intro w hqw
    by_cases hw : w ∈ G
    · unfold condLaw
      rw [if_pos hw]
      exact div_pos (hp w) hmass
    · exact absurd (hsupp w hw) (ne_of_gt hqw)

/-- **`(12)`, attainment.**  The conditioned reference is an admissible encoder whose synthesis
divergence is exactly the negative log mass. -/
theorem relEntropy_condLaw_eq_neg_log {p : α → ℝ} (G : Set α) {mass : ℝ} (hmass : 0 < mass)
    (hp : ∀ w, 0 < p w) (hcond : HasSum (condLaw p G mass) 1) :
    relEntropy (condLaw p G mass) p = -Real.log mass := by
  classical
  have hpoint : ∀ w, condLaw p G mass w * Real.log (condLaw p G mass w / p w) =
      condLaw p G mass w * (-Real.log mass) := by
    intro w
    unfold condLaw
    by_cases hw : w ∈ G
    · rw [if_pos hw]
      congr 1
      rw [show p w / mass / p w = (mass)⁻¹ by
        field_simp
        exact div_self (ne_of_gt (hp w)), Real.log_inv]
    · rw [if_neg hw]
      ring
  unfold relEntropy
  rw [tsum_congr hpoint, tsum_mul_right, hcond.tsum_eq, one_mul]

end Conditioning

section Tail

variable {Γ : Type*} [Fintype Γ]

/-- Splitting a long word into its first `n` letters and the rest. -/
def longWordEquiv (Γ : Type*) (n : ℕ) :
    (List.Vector Γ n × List Γ) ≃ {w : List Γ // n ≤ w.length} where
  toFun uv := ⟨uv.1.1 ++ uv.2, by simp [uv.1.2]⟩
  invFun w := (⟨w.1.take n, by simp [min_eq_left w.2]⟩, w.1.drop n)
  left_inv := by
    rintro ⟨⟨u, hu⟩, v⟩
    ext1
    · apply Subtype.ext
      exact List.take_left' hu
    · exact List.drop_left' hu
  right_inv := by
    rintro ⟨w, hw⟩
    apply Subtype.ext
    exact List.take_append_drop n w

theorem wordPrior_append {a : ℝ} {n : ℕ} (u : List.Vector Γ n) (v : List Γ) :
    wordPrior a (u.1 ++ v) = (a / (Fintype.card Γ : ℝ)) ^ n * wordPrior a v := by
  unfold wordPrior
  rw [List.length_append, u.2, pow_add]
  ring

/-- **The geometric length tail.**  The prior mass of the words of length at least `n` is `aⁿ`. -/
theorem tsum_wordPrior_long {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    (n : ℕ) :
    ∑' w : {w : List Γ // n ≤ w.length}, wordPrior a w.1 = a ^ n := by
  classical
  have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
  have hnn : ∀ w : List Γ, 0 ≤ wordPrior (Γ := Γ) a w :=
    fun w => le_of_lt (wordPrior_pos ha ha1 hM w)
  have htotal := hasSum_wordPrior (Γ := Γ) ha ha1 hM
  have hsummable : Summable (wordPrior (Γ := Γ) a) := htotal.summable
  have hsub : Summable (fun w : {w : List Γ // n ≤ w.length} => wordPrior (Γ := Γ) a w.1) :=
    hsummable.subtype _
  have hshift : (0 : ℝ) ≤ (a / (Fintype.card Γ : ℝ)) ^ n := by positivity
  have hfiber : ∀ u : List.Vector Γ n,
      HasSum (fun v : List Γ => wordPrior (Γ := Γ) a (u.1 ++ v))
        ((a / (Fintype.card Γ : ℝ)) ^ n) := by
    intro u
    have hbase := htotal.mul_left ((a / (Fintype.card Γ : ℝ)) ^ n)
    rw [mul_one] at hbase
    exact hbase.congr_fun fun v => wordPrior_append u v
  have hsummableProd : Summable (fun uv : List.Vector Γ n × List Γ =>
      wordPrior (Γ := Γ) a (uv.1.1 ++ uv.2)) :=
    ((longWordEquiv Γ n).summable_iff (f := fun w : {w : List Γ // n ≤ w.length} =>
      wordPrior (Γ := Γ) a w.1)).mpr hsub
  have hval : (∑' uv : List.Vector Γ n × List Γ,
      wordPrior (Γ := Γ) a (uv.1.1 ++ uv.2)) = a ^ n := by
    rw [hsummableProd.tsum_prod' fun u => (hfiber u).summable]
    have hinner : ∀ u : List.Vector Γ n,
        (∑' v : List Γ, wordPrior (Γ := Γ) a (u.1 ++ v)) =
          (a / (Fintype.card Γ : ℝ)) ^ n := fun u => (hfiber u).tsum_eq
    rw [tsum_congr hinner, tsum_fintype, Finset.sum_const, Finset.card_univ, card_vector,
      nsmul_eq_mul]
    push_cast
    rw [div_pow]
    field_simp
  rw [← (longWordEquiv Γ n).tsum_eq (fun w : {w : List Γ // n ≤ w.length} =>
    wordPrior (Γ := Γ) a w.1)]
  exact hval

/-- **`(16)`.**  If every admissible word is long, the admissible mass is geometrically small. -/
theorem admissibleMass_le_of_long {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    {G : Set (List Γ)} {n : ℕ} (hG : ∀ w ∈ G, n ≤ w.length)
    {mass : ℝ} (hmass : HasSum (fun w : G => wordPrior a w.1) mass) :
    mass ≤ a ^ n := by
  classical
  have hnn : ∀ w : List Γ, 0 ≤ wordPrior (Γ := Γ) a w :=
    fun w => le_of_lt (wordPrior_pos ha ha1 hM w)
  have hsummable : Summable (wordPrior (Γ := Γ) a) :=
    (hasSum_wordPrior (Γ := Γ) ha ha1 hM).summable
  have hsub : Summable (fun w : {w : List Γ // n ≤ w.length} => wordPrior (Γ := Γ) a w.1) :=
    hsummable.subtype _
  have hinj : Function.Injective
      (fun w : G => (⟨w.1, hG w.1 w.2⟩ : {w : List Γ // n ≤ w.length})) := by
    intro w₁ w₂ h
    apply Subtype.ext
    exact congrArg (Subtype.val : {w : List Γ // n ≤ w.length} → List Γ) h
  have hle := Summable.tsum_le_tsum_of_inj
    (fun w : G => (⟨w.1, hG w.1 w.2⟩ : {w : List Γ // n ≤ w.length}))
    hinj (fun c _ => hnn c.1) (fun b => le_rfl) hmass.summable hsub
  rw [hmass.tsum_eq, tsum_wordPrior_long ha ha1 hM n] at hle
  exact hle

/-- **`(16)`.**  Hence the hard Green surprisal is at least the geometric length cost. -/
theorem le_neg_log_admissibleMass {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    {G : Set (List Γ)} {n : ℕ} (hG : ∀ w ∈ G, n ≤ w.length)
    {mass : ℝ} (hmasspos : 0 < mass) (hmass : HasSum (fun w : G => wordPrior a w.1) mass) :
    (n : ℝ) * Real.log (1 / a) ≤ -Real.log mass := by
  have hle := admissibleMass_le_of_long ha ha1 hM hG hmass
  have hlog : Real.log mass ≤ Real.log (a ^ n) :=
    Real.log_le_log hmasspos hle
  rw [Real.log_pow] at hlog
  rw [one_div, Real.log_inv]
  linarith

/-- **`(17)`.**  One admissible witness word caps the hard Green surprisal. -/
theorem neg_log_admissibleMass_le {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    {G : Set (List Γ)} {w₀ : List Γ} (hw₀ : w₀ ∈ G)
    {mass : ℝ} (hmass : HasSum (fun w : G => wordPrior a w.1) mass) :
    -Real.log mass ≤
      -Real.log (1 - a) + (w₀.length : ℝ) * Real.log ((Fintype.card Γ : ℝ) / a) := by
  classical
  have hnn : ∀ w : List Γ, 0 ≤ wordPrior (Γ := Γ) a w :=
    fun w => le_of_lt (wordPrior_pos ha ha1 hM w)
  have hwitness : wordPrior (Γ := Γ) a w₀ ≤ mass :=
    le_hasSum hmass (⟨w₀, hw₀⟩ : G) (fun j _ => hnn j.1)
  have hpos : 0 < wordPrior (Γ := Γ) a w₀ := wordPrior_pos ha ha1 hM w₀
  have hlog : Real.log (wordPrior (Γ := Γ) a w₀) ≤ Real.log mass :=
    Real.log_le_log hpos hwitness
  have := neg_log_wordPrior (Γ := Γ) ha ha1 hM w₀
  linarith [this]

end Tail

end

end GaloisForLFunctions.HTGeometry
