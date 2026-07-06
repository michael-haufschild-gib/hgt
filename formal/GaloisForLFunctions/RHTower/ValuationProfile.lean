import GaloisForLFunctions.RHTower.Variation

/-!
# The 2-adic valuation profile and the filtration length

The jump divisor `discJump t` is a natural number; its 2-adic valuation grades the whole rung
filtration.  The **valuation profile** `valProfile t = emultiplicity 2 (discJump t) ∈ ℕ∞` is a
line-native function whose sub-`k` level set is exactly the variation zero-set:
`badHeightSet k = {t | valProfile t < k}`.  Its value is `⊤` precisely at the non-zero-heights, so
RH is the statement that the profile is identically `⊤`.

On the zero heights (`discJump t ≠ 0`) the profile is finite and equals the **filtration length**
`filtrationLength t = (discJump t).factorization 2` — the last level `k` at which the height passes
(`2^k ∣ discJump t`).  Over a height window the minimal filtration length is the **window depth**
`windowDepth T ∈ ℕ∞`, a single finite certificate with `V k T = 0 ↔ k ≤ windowDepth T`.  The length
is transport-shadowable: where ξ's and the finite carrier's divisibility criteria agree at every
level, the two filtration lengths coincide.
-/

namespace RHTower

open Complex Set Metric

/-! ## The 2-adic valuation profile -/

/-- **The 2-adic valuation profile**: the 2-adic valuation of the jump divisor, valued in `ℕ∞`
(`⊤` where the jump vanishes). -/
noncomputable def valProfile (t : ℝ) : ℕ∞ := emultiplicity 2 (discJump t)

/-- `2^k` divides the jump iff `k` is below the valuation. -/
theorem pow_dvd_discJump_iff_le_valProfile (k : ℕ) (t : ℝ) :
    2 ^ k ∣ discJump t ↔ (k : ℕ∞) ≤ valProfile t :=
  pow_dvd_iff_le_emultiplicity

/-- **The variation zero-set is a level set of the valuation profile.**  A height is `k`-failing
exactly when its valuation is below `k`: the `badHeightSet`s are the sub-`k` cuts of the profile. -/
theorem badHeightSet_eq_valProfile_lt (k : ℕ) :
    badHeightSet k = {t : ℝ | valProfile t < (k : ℕ∞)} := by
  ext t
  rw [badHeightSet, Set.mem_setOf_eq, Set.mem_setOf_eq, pow_dvd_discJump_iff_le_valProfile, not_le]

/-- The filtration is increasing: a `k`-failing height is `(k+1)`-failing. -/
theorem badHeightSet_subset_succ (k : ℕ) : badHeightSet k ⊆ badHeightSet (k + 1) := by
  intro t ht
  simp only [badHeightSet_eq_valProfile_lt, Set.mem_setOf_eq] at ht ⊢
  exact lt_of_lt_of_le ht (by exact_mod_cast Nat.le_succ k)

/-- The profile is `⊤` exactly at the non-zero-heights. -/
theorem valProfile_eq_top_iff (t : ℝ) : valProfile t = ⊤ ↔ discJump t = 0 := by
  rw [valProfile, emultiplicity_eq_top]
  constructor
  · intro h
    by_contra hn
    exact h (Nat.finiteMultiplicity_iff.mpr ⟨by norm_num, Nat.pos_of_ne_zero hn⟩)
  · intro h
    rw [h]
    simp [Nat.finiteMultiplicity_iff]

/-- **RH as a constant valuation profile.**  RH holds iff the valuation profile is identically `⊤`:
every height has infinite 2-adic valuation, i.e. carries no off-line ξ-order. -/
theorem rh_iff_forall_valProfile_eq_top :
    RiemannHypothesis ↔ ∀ t : ℝ, valProfile t = ⊤ := by
  rw [rh_iff_forall_discJump_eq_zero]
  exact forall_congr' fun t => (valProfile_eq_top_iff t).symm

/-! ## The filtration length -/

/-- **The filtration length** at a height: the 2-adic valuation of the jump divisor as a natural
number — the last level `k` at which the height passes the rung. -/
noncomputable def filtrationLength (t : ℝ) : ℕ := (discJump t).factorization 2

/-- On a zero height, `2^k` divides the jump iff `k` is at most the filtration length. -/
theorem pow_dvd_discJump_iff_le_filtrationLength {t : ℝ} (hne : discJump t ≠ 0) (k : ℕ) :
    2 ^ k ∣ discJump t ↔ k ≤ filtrationLength t :=
  Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne

/-- On a zero height the valuation profile is the (finite) filtration length. -/
theorem valProfile_eq_filtrationLength {t : ℝ} (hne : discJump t ≠ 0) :
    valProfile t = (filtrationLength t : ℕ∞) := by
  rw [valProfile, filtrationLength]
  apply le_antisymm
  · have hnd : ¬ (2 : ℕ) ^ ((discJump t).factorization 2 + 1) ∣ discJump t := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne]; omega
    have hlt : emultiplicity 2 (discJump t) < (((discJump t).factorization 2 + 1 : ℕ) : ℕ∞) := by
      rw [← not_le, ← pow_dvd_iff_le_emultiplicity]; exact hnd
    rw [Nat.cast_add, Nat.cast_one] at hlt
    exact ENat.lt_coe_add_one_iff.mp hlt
  · rw [← pow_dvd_iff_le_emultiplicity]
    exact Nat.ordProj_dvd (discJump t) 2

/-- A box ξ-zero forces its height's jump divisor to be nonzero. -/
theorem discJump_ne_zero_of_mem_boxZeros {T : ℝ} {z : ℂ} (hz : z ∈ boxZeros T) :
    discJump z.im ≠ 0 := by
  intro h
  rw [discJump_eq_zero_iff] at h
  have hmem : z ∈ boxHeightZeros z.im := ⟨hz.1.1, hz.1.2.1, rfl, hz.2⟩
  rw [h] at hmem
  exact absurd hmem (Set.notMem_empty z)

/-- A height failing the rung is `k`-failing iff its filtration length is below `k`. -/
theorem mem_badHeightSet_iff_filtrationLength_lt {t : ℝ} (hne : discJump t ≠ 0) (k : ℕ) :
    t ∈ badHeightSet k ↔ filtrationLength t < k := by
  rw [badHeightSet, Set.mem_setOf_eq, pow_dvd_discJump_iff_le_filtrationLength hne, not_le]

/-! ## The window depth: a finite certificate -/

/-- **The window depth**: the minimal filtration length over the box zeros below `T`, valued in
`ℕ∞` (`⊤` when the window is zero-free). -/
noncomputable def windowDepth (T : ℝ) : ℕ∞ :=
  ((boxFinset T).image Complex.im).inf (fun t => (filtrationLength t : ℕ∞))

/-- **The window depth is the exact rung reach.**  The variation vanishes through level `k` iff `k`
is at most the window depth: a single finite certificate summarising every level at once. -/
theorem V_eq_zero_iff_le_windowDepth (k : ℕ) (T : ℝ) :
    V k T = 0 ↔ (k : ℕ∞) ≤ windowDepth T := by
  rw [V_eq_zero_iff, windowDepth, Finset.le_inf_iff]
  constructor
  · intro h t ht
    obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
    have hzbox := mem_boxFinset.mp hz
    have hne : discJump t ≠ 0 := hzt ▸ discJump_ne_zero_of_mem_boxZeros hzbox
    have hdvd : 2 ^ k ∣ discJump t := hzt ▸ h z hzbox
    exact_mod_cast (pow_dvd_discJump_iff_le_filtrationLength hne k).mp hdvd
  · intro h z hz
    have hmem : z.im ∈ (boxFinset T).image Complex.im :=
      Finset.mem_image_of_mem _ (mem_boxFinset.mpr hz)
    have hne : discJump z.im ≠ 0 := discJump_ne_zero_of_mem_boxZeros hz
    have hle : (k : ℕ∞) ≤ (filtrationLength z.im : ℕ∞) := h z.im hmem
    exact (pow_dvd_discJump_iff_le_filtrationLength hne k).mpr (by exact_mod_cast hle)

/-- The window depth is finite exactly when the window carries a box ξ-zero. -/
theorem windowDepth_lt_top_iff (T : ℝ) :
    windowDepth T < ⊤ ↔ ((boxFinset T).image Complex.im).Nonempty := by
  rw [windowDepth]
  constructor
  · intro h
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.inf_empty] at h
    exact absurd h (lt_irrefl ⊤)
  · intro ⟨t, ht⟩
    exact lt_of_le_of_lt (Finset.inf_le ht) (by exact_mod_cast ENat.coe_lt_top _)

/-! ## The transport shadow of the filtration length -/

/-- The finite carrier's filtration length at a height. -/
noncomputable def finiteFiltrationLength (H : ℝ → Finset ℂ) (mg : ℂ → ℕ) (t : ℝ) : ℕ :=
  (finiteDiscJump H mg t).factorization 2

/-- **The filtration length is transport-shadowable.**  Where ξ's and the finite carrier's
divisibility criteria agree at every level — the family of `dvd_discJump_iff_finiteDiscJump` — the
two filtration lengths coincide, so the length is a decidable finite-carrier datum. -/
theorem filtrationLength_eq_finite {H : ℝ → Finset ℂ} {mg : ℂ → ℕ} {t : ℝ}
    (hne : discJump t ≠ 0) (hne' : finiteDiscJump H mg t ≠ 0)
    (hshadow : ∀ k : ℕ, 2 ^ k ∣ discJump t ↔ 2 ^ k ∣ finiteDiscJump H mg t) :
    filtrationLength t = finiteFiltrationLength H mg t := by
  apply le_antisymm
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne').mp
      ((hshadow _).mp (Nat.ordProj_dvd (discJump t) 2))
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp
      ((hshadow _).mpr (Nat.ordProj_dvd (finiteDiscJump H mg t) 2))

end RHTower
