import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreFibre
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety

/-!
# Prime homothety of processed-core coordinates

At a prime dilation cutoff, processing the dilation prime transports each
literal processed-core coordinate exactly.  The coordinate moves to the core
with that prime inserted, changes its raw sign, and gains a square-root scale
factor.  Consequently a pair of old core coordinates is replicated with the
positive factor `p`; prime dilation alone preserves every reinforcing
core-parity correlation instead of dissipating it.
-/

noncomputable section
open Finset
namespace RHTower

/-- The processed-core coordinate may be summed over the full arithmetic
interval: nonsquarefree and terminal channels vanish. -/
private theorem processedCoreFibre_eq_sum_Icc
    (M : ℕ) (P A R : Finset ℕ) :
    mobiusDivisorSelectionProcessedCoreFibre M P A R =
      ∑ d ∈ Icc 1 M,
        if d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A then
          mobiusDivisorDilationChannel M d
        else 0 := by
  unfold mobiusDivisorSelectionProcessedCoreFibre
  calc
    _ = ∑ d ∈ Icc 1 (M - 1),
        if d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A then
          mobiusDivisorDilationChannel M d
        else 0 := by
      rw [mobiusDivisorSelectionIndices, sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hs : Squarefree d
      · simp [hs]
      · have hz : mobiusDivisorDilationChannel M d = 0 := by
          simp [mobiusDivisorDilationChannel,
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
        simp [hs, hz]
    _ = _ := by
      apply sum_subset
      · intro d hd
        obtain ⟨hl, hu⟩ := mem_Icc.mp hd
        exact mem_Icc.mpr ⟨hl, by omega⟩
      · intro d hd hn
        have heq : d = M := by
          simp only [mem_Icc] at hd hn
          omega
        subst d
        have hz : mobiusDivisorDilationChannel M M = 0 := by
          have hM : 0 < M := (mem_Icc.mp hd).1
          simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (by omega : M - 1 < M)]
        simp [hz]

/-- Processing a dilation prime moves every old processed-core coordinate to
the parity-opposite core as an exact reflected square-root copy. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P A R : Finset ℕ) (hpA : p ∉ A) :
    mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R =
      -Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P A R := by
  rw [processedCoreFibre_eq_sum_Icc, processedCoreFibre_eq_sum_Icc]
  have hrestrict :
      (∑ n ∈ Icc 1 (p * N),
        if n.primeFactors \ insert p P = R ∧ n.primeFactors ∩ insert p P = insert p A then
          mobiusDivisorDilationChannel (p * N) n
        else 0) =
      ∑ n ∈ (Icc 1 (p * N)).filter (fun n => p ∣ n),
        if n.primeFactors \ insert p P = R ∧ n.primeFactors ∩ insert p P = insert p A then
          mobiusDivisorDilationChannel (p * N) n
        else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hpn : p ∣ n
    · simp [hpn]
    · have hne : ¬(n.primeFactors \ insert p P = R ∧
          n.primeFactors ∩ insert p P = insert p A) := by
        intro h
        have hm : p ∈ n.primeFactors :=
          (mem_inter.mp (h.2 ▸ mem_insert_self p A)).1
        exact hpn (Nat.mem_primeFactors.mp hm).2.1
      rw [if_neg hne]
      simp [hpn]
  rw [hrestrict, sum_Icc_filter_dvd_reindex p (p * N) hp.pos,
    Nat.mul_div_cancel_left N hp.pos, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (mem_Icc.mp hn).1
    omega
  have hpndvd : ¬p ∣ n := by
    intro h
    have hle := Nat.le_of_dvd (mem_Icc.mp hn).1 h
    have hu := (mem_Icc.mp hn).2
    omega
  have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpndvd
  have hpN : p ∉ n.primeFactors := fun h => hpndvd (Nat.mem_primeFactors.mp h).2.1
  have hpf : (p * n).primeFactors = insert p n.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hn0, hp.primeFactors]
    simp
  have hdiff : (insert p n.primeFactors) \ insert p P = n.primeFactors \ P := by
    ext q
    by_cases hq : q = p
    · subst q
      simp [hpN]
    · simp [hq]
  have hinter : (insert p n.primeFactors) ∩ insert p P =
      insert p (n.primeFactors ∩ P) := by
    ext q
    by_cases hq : q = p
    · subst q
      simp
    · simp [hq]
  have hlabels :
      (p * n).primeFactors \ insert p P = R ∧
          (p * n).primeFactors ∩ insert p P = insert p A ↔
        n.primeFactors \ P = R ∧ n.primeFactors ∩ P = A := by
    rw [hpf, hdiff, hinter]
    constructor
    · rintro ⟨hres, hcore⟩
      refine ⟨hres, ?_⟩
      ext q
      by_cases hq : q = p
      · subst q
        simp [hpN, hpA]
      · have h := Finset.ext_iff.mp hcore q
        simpa [hq] using h
    · rintro ⟨hres, hcore⟩
      exact ⟨hres, by rw [hcore]⟩
  by_cases h : n.primeFactors \ P = R ∧ n.primeFactors ∩ P = A
  · rw [if_pos (hlabels.mpr h), if_pos h, mobiusDivisorDilationChannel_mul_coprime hc,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  · rw [if_neg (fun h' => h (hlabels.mp h')), if_neg h, mul_zero]

/-- In canonical core--residual orientation the copied coordinate remains
positive and gains exactly the square-root scale factor. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_oriented_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P A R : Finset ℕ) (hpA : p ∉ A) :
    (-1 : ℝ) ^ ((insert p A).card + R.card) *
        mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R =
      Real.sqrt p *
        ((-1 : ℝ) ^ (A.card + R.card) *
          mobiusDivisorSelectionProcessedCoreFibre N P A R) := by
  rw [mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P A R hpA,
    card_insert_of_notMem hpA]
  rw [show A.card + 1 + R.card = (A.card + R.card) + 1 by omega, pow_succ]
  ring

/-- A processed dilation preserves every old core-pair correlation up to the
positive factor `p`; replication alone cannot reverse a reinforcing
opposite-parity sector. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime_pair
    {N p q : ℕ} (hp : p.Prime) (hNp : N < p)
    (P A B R : Finset ℕ) (hpA : p ∉ A) (hpB : p ∉ B) :
    mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R *
      mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p B)
        (insert q R) =
      (p : ℝ) *
        (mobiusDivisorSelectionProcessedCoreFibre N P A R *
          mobiusDivisorSelectionProcessedCoreFibre N P B (insert q R)) := by
  rw [mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P A R hpA,
    mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P B (insert q R) hpB]
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p :=
    Real.mul_self_sqrt (Nat.cast_nonneg p)
  calc
    (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P A R) *
        (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P B (insert q R)) =
        (Real.sqrt p * Real.sqrt p) *
          (mobiusDivisorSelectionProcessedCoreFibre N P A R *
            mobiusDivisorSelectionProcessedCoreFibre N P B (insert q R)) := by ring
    _ = _ := by rw [hsqrt]

/-- The total nonnegative square mass of processed-core coordinates at each
fixed residual label cannot contract under a processed prime dilation.  The
copied `p`-containing core slice already has exactly `p` times the old mass. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_square_mass_insert_mul_prime_le
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) :
    (p : ℝ) *
        (∑ A ∈ P.powerset,
          (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ)) ≤
      ∑ B ∈ (insert p P).powerset,
        (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) B R)^(2 : ℕ) := by
  have hsplit (f : Finset ℕ → ℝ) :
      (∑ B ∈ (insert p P).powerset, f B) =
        (∑ A ∈ P.powerset, f A) + ∑ A ∈ P.powerset, f (insert p A) := by
    exact sum_powerset_insert hpP f
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p :=
    Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hcopy :
      (∑ A ∈ P.powerset,
        (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R)^(2 : ℕ)) =
        (p : ℝ) *
          (∑ A ∈ P.powerset,
            (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro A hA
    have hpA : p ∉ A := by
      intro h
      exact hpP (mem_powerset.mp hA h)
    rw [mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P A R hpA]
    calc
      (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ) =
          (Real.sqrt p * Real.sqrt p) *
            (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ) := by ring
      _ = _ := by rw [hsqrt]
  rw [hsplit, hcopy]
  have hnon : 0 ≤ ∑ A ∈ P.powerset,
      (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) A R)^(2 : ℕ) := by
    apply sum_nonneg
    intro A hA
    exact sq_nonneg _
  linarith only [hnon]

/-- The same expansion law holds for every nonnegative diagonal metric that
is compatible with the prime-copy embedding of processed cores.  Thus no
copy-respecting positive core-coordinate weighting can supply a contracting
CCM-FU budget. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_weighted_square_mass_insert_mul_prime_le
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) (w : Finset ℕ → ℝ)
    (hw_nonneg : ∀ B ∈ (insert p P).powerset, 0 ≤ w B)
    (hw_copy : ∀ A ∈ P.powerset, w (insert p A) = w A) :
    (p : ℝ) *
        (∑ A ∈ P.powerset,
          w A * (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ)) ≤
      ∑ B ∈ (insert p P).powerset,
        w B * (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) B R)^(2 : ℕ) := by
  have hsplit (f : Finset ℕ → ℝ) :
      (∑ B ∈ (insert p P).powerset, f B) =
        (∑ A ∈ P.powerset, f A) + ∑ A ∈ P.powerset, f (insert p A) := by
    exact sum_powerset_insert hpP f
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p :=
    Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hcopy :
      (∑ A ∈ P.powerset,
        w (insert p A) *
          (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R)^(2 : ℕ)) =
        (p : ℝ) *
          (∑ A ∈ P.powerset,
            w A * (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro A hA
    have hpA : p ∉ A := by
      intro h
      exact hpP (mem_powerset.mp hA h)
    rw [hw_copy A hA,
      mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P A R hpA]
    calc
      w A * (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ) =
          (Real.sqrt p * Real.sqrt p) *
            (w A * (mobiusDivisorSelectionProcessedCoreFibre N P A R)^(2 : ℕ)) := by ring
      _ = _ := by rw [hsqrt]
  rw [hsplit, hcopy]
  have hnon : 0 ≤ ∑ A ∈ P.powerset,
      w A *
        (mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) A R)^(2 : ℕ) := by
    apply sum_nonneg
    intro A hA
    apply mul_nonneg
    · apply hw_nonneg A
      apply mem_powerset.mpr
      exact (mem_powerset.mp hA).trans (subset_insert _ _)
    · exact sq_nonneg _
  linarith only [hnon]

/-- Processing a prime leaves a core/residual coordinate untouched when that
coordinate contains neither the new processed prime in its core nor in its
residual label. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_insert_pfree
    (M p : ℕ) (P A R : Finset ℕ) (hpA : p ∉ A) (hpR : p ∉ R) :
    mobiusDivisorSelectionProcessedCoreFibre M (insert p P) A R =
      mobiusDivisorSelectionProcessedCoreFibre M P A R := by
  unfold mobiusDivisorSelectionProcessedCoreFibre
  apply sum_congr rfl
  intro d hd
  have hlabels :
      (d.primeFactors \ insert p P = R ∧ d.primeFactors ∩ insert p P = A) ↔
        (d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A) := by
    constructor
    · intro h
      have hpD : p ∉ d.primeFactors := by
        intro hpD
        have hpnew : p ∈ d.primeFactors ∩ insert p P :=
          mem_inter.mpr ⟨hpD, mem_insert_self p P⟩
        rw [h.2] at hpnew
        exact hpA hpnew
      rw [sdiff_insert_of_notMem hpD, inter_insert_of_notMem hpD] at h
      exact h
    · intro h
      have hpD : p ∉ d.primeFactors := by
        intro hpD
        by_cases hpP : p ∈ P
        · have hpold : p ∈ d.primeFactors ∩ P := mem_inter.mpr ⟨hpD, hpP⟩
          rw [h.2] at hpold
          exact hpA hpold
        · have hpold : p ∈ d.primeFactors \ P := mem_sdiff.mpr ⟨hpD, hpP⟩
          rw [h.1] at hpold
          exact hpR hpold
      rw [sdiff_insert_of_notMem hpD, inter_insert_of_notMem hpD]
      exact h
  simp only [hlabels]

/-- At a prime dilation, canonical positive processed-core mass splits
exactly into the p-free large-cutoff background and the reflected
smaller-cutoff copy. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_oriented_mass_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    (∑ B ∈ (insert p P).powerset,
      (-1 : ℝ) ^ (B.card + R.card) *
        mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) B R) =
      (∑ A ∈ P.powerset,
        (-1 : ℝ) ^ (A.card + R.card) *
          mobiusDivisorSelectionProcessedCoreFibre (p * N) P A R) +
        Real.sqrt p *
          ∑ A ∈ P.powerset,
            (-1 : ℝ) ^ (A.card + R.card) *
              mobiusDivisorSelectionProcessedCoreFibre N P A R := by
  rw [sum_powerset_insert hpP]
  congr 1
  · apply sum_congr rfl
    intro A hA
    have hpA : p ∉ A := fun h => hpP (mem_powerset.mp hA h)
    rw [mobiusDivisorSelectionProcessedCoreFibre_insert_pfree
      (p * N) p P A R hpA hpR]
  · rw [mul_sum]
    apply sum_congr rfl
    intro A hA
    have hpA : p ∉ A := fun h => hpP (mem_powerset.mp hA h)
    rw [mobiusDivisorSelectionProcessedCoreFibre_oriented_insert_mul_prime
      hp hNp P A R hpA]

end RHTower
