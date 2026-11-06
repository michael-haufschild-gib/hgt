import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeReadsThePrimesCausally
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheEvolutionStartsPositive
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheDatumIsTheSzegoThreshold

/-!
# Inverse scattering with prime data

A lattice medium is its reflection data, and for `Spec ℤ` the reflection data read the primes.

**Free coordinates** (`exists_evenSeq_of_reflCoeff`, `evenSeq_eq_of_reflCoeff_eq`). Every sequence in `(−1, 1)`, with every `κ₀ > 0`, is the reflection data of exactly
one passive even sequence. So a passive medium is built echo by echo:
`κ(n + 1) = π_n + γ_nE_n`, with `π_n` the frozen prediction. **An echo train is passive iff each echo lies in its Schur band**
`(π_n − E_n, π_n + E_n)` (`passive_iff_each_echo_in_band`), and a band can be filled in any way: positivity puts no constraint on the
reflection data beyond the size of each coordinate.

**The prime dictionary.** Let `φ` be a short bump, with step `h = log n₀`. The prime `n₀` meets the lattice in its first echo:
* `κ^λ(1) − κ^{λ'}(1) = −((λ(n₀) − λ'(n₀))/√n₀) ‖φ‖²` if the weights differ only at `n₀` (`weilSeqW_one_sub`);
* the first reflector moves by that amount over `Q(φ)` (`reflCoeff_zero_sub`), and the central datum `κ(0) = Q(φ)` does not read any weight (`weilSeqW_zero_eq_weilQuad`);
* for `Spec ℤ`, `Λ(n₀)` is an explicit function of `γ₀` and of the data without the prime `n₀` (`vonMangoldt_eq_of_reflCoeff`).

**Uniqueness** (`weight_eq_of_reflCoeff_eq`). Two prime weights with equal first reflectors on the short bumps are equal. So the forward map from prime data to
reflection data, causal and triangular in `n` by the locality of the lattice, is injective.
-/

open Finset Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

noncomputable section

/-! ### Free coordinates -/

/-- Place the echo `t` at the sites `±(n + 1)`. -/
def addEcho (κ : ℤ → ℝ) (n : ℕ) (t : ℝ) (d : ℤ) : ℝ :=
  if d = (n : ℤ) + 1 ∨ d = -((n : ℤ) + 1) then t else κ d

/-- The medium with reflection data `γ`, built up to size `n`. -/
def echoChain (κ₀ : ℝ) (γ : ℕ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun d => if d = 0 then κ₀ else 0
  | n + 1 => addEcho (echoChain κ₀ γ n) n
      (frozenPrediction (echoChain κ₀ γ n) n (levinsonPred (echoChain κ₀ γ n) n) +
        γ n * levinsonErr (echoChain κ₀ γ n) n)

/-- The medium with reflection data `γ`. -/
def echoSeq (κ₀ : ℝ) (γ : ℕ → ℝ) (d : ℤ) : ℝ := echoChain κ₀ γ d.natAbs d

variable {κ₀ : ℝ} {γ : ℕ → ℝ}

theorem echoChain_succ_of_le {n : ℕ} {d : ℤ} (hd : d.natAbs ≤ n) :
    echoChain κ₀ γ (n + 1) d = echoChain κ₀ γ n d := by
  rw [echoChain, addEcho, if_neg]
  omega

theorem echoChain_of_le {n m : ℕ} (hnm : n ≤ m) {d : ℤ} (hd : d.natAbs ≤ n) :
    echoChain κ₀ γ m d = echoChain κ₀ γ n d := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [echoChain_succ_of_le (hd.trans hm), ih]

theorem echoSeq_eq {n : ℕ} {d : ℤ} (hd : d.natAbs ≤ n) : echoSeq κ₀ γ d = echoChain κ₀ γ n d :=
  (echoChain_of_le hd le_rfl).symm

theorem echoChain_isEven (n : ℕ) : IsEvenSeq (echoChain κ₀ γ n) := by
  induction n with
  | zero =>
    intro d
    simp [echoChain]
  | succ n ih =>
    intro d
    simp only [echoChain, addEcho]
    by_cases h : d = (n : ℤ) + 1 ∨ d = -((n : ℤ) + 1)
    · have h' : -d = (n : ℤ) + 1 ∨ -d = -((n : ℤ) + 1) := by omega
      rw [if_pos h, if_pos h']
    · have h' : ¬(-d = (n : ℤ) + 1 ∨ -d = -((n : ℤ) + 1)) := by omega
      rw [if_neg h, if_neg h', ih]

theorem echoSeq_isEven : IsEvenSeq (echoSeq κ₀ γ) := fun d => by
  rw [echoSeq, Int.natAbs_neg, echoChain_isEven, echoSeq]

theorem levinson_echoSeq (n : ℕ) : levinson (echoSeq κ₀ γ) n = levinson (echoChain κ₀ γ n) n :=
  levinson_congr n fun d hd => echoSeq_eq (by simpa using hd)

theorem levinsonErr_echoSeq (n : ℕ) :
    levinsonErr (echoSeq κ₀ γ) n = levinsonErr (echoChain κ₀ γ n) n := by
  rw [levinsonErr, levinson_echoSeq, levinsonErr]

theorem levinsonPred_echoSeq (n : ℕ) :
    levinsonPred (echoSeq κ₀ γ) n = levinsonPred (echoChain κ₀ γ n) n := by
  rw [levinsonPred, levinson_echoSeq, levinsonPred]

/-- The frozen prediction reads only the sites up to `n`. -/
theorem frozenPrediction_congr {κ κ' : ℤ → ℝ} {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ d : ℕ, d ≤ n → κ d = κ' d) : frozenPrediction κ n a = frozenPrediction κ' n a := by
  simp only [frozenPrediction]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 1
  have hk := k.isLt
  exact_mod_cast h (k + 1) (by omega)

/-- **The Schur parameter of the built medium is the prescribed one.** -/
theorem schurParam_echoSeq (n : ℕ) :
    schurParam (echoSeq κ₀ γ) n = γ n * levinsonErr (echoSeq κ₀ γ) n := by
  rw [schurParam_eq, levinsonPred_echoSeq, levinsonErr_echoSeq,
    frozenPrediction_congr (κ' := echoChain κ₀ γ n) _ fun d hd => echoSeq_eq (by simpa using hd)]
  have h1 : echoSeq κ₀ γ ((n : ℤ) + 1) = echoChain κ₀ γ (n + 1) ((n : ℤ) + 1) :=
    echoSeq_eq (by omega)
  have h2 : echoChain κ₀ γ (n + 1) ((n : ℤ) + 1) =
      frozenPrediction (echoChain κ₀ γ n) n (levinsonPred (echoChain κ₀ γ n) n) +
        γ n * levinsonErr (echoChain κ₀ γ n) n := by
    rw [echoChain, addEcho, if_pos (Or.inl rfl)]
  rw [h1, h2]
  ring

theorem echoSeq_zero : echoSeq κ₀ γ 0 = κ₀ := by simp [echoSeq, echoChain]

/-- **Existence.** Every sequence in `(−1, 1)` is the reflection data of a passive even sequence. -/
theorem exists_evenSeq_of_reflCoeff (h0 : 0 < κ₀) (hγ : ∀ n, |γ n| < 1) :
    ∃ κ : ℤ → ℝ, IsEvenSeq κ ∧ κ 0 = κ₀ ∧ (∀ n, reflCoeff κ n = γ n) ∧
      ∀ n, ToeplitzPosDef κ (n + 1) := by
  have hE : ∀ n, 0 < levinsonErr (echoSeq κ₀ γ) n := by
    intro n
    induction n with
    | zero => rw [levinsonErr_zero, echoSeq_zero]; exact h0
    | succ n ih =>
      rw [levinsonErr_succ, schurParam_echoSeq]
      have h1 := (sq_lt_one_iff_abs_lt_one _).mpr (hγ n)
      have e : levinsonErr (echoSeq κ₀ γ) n - (γ n * levinsonErr (echoSeq κ₀ γ) n) ^ 2 /
          levinsonErr (echoSeq κ₀ γ) n = levinsonErr (echoSeq κ₀ γ) n * (1 - γ n ^ 2) := by
        field_simp
      rw [e]
      exact mul_pos ih (by linarith)
  refine ⟨echoSeq κ₀ γ, echoSeq_isEven, echoSeq_zero, fun n => ?_, fun n => ?_⟩
  · rw [reflCoeff, schurParam_echoSeq]
    exact mul_div_cancel_right₀ _ (hE n).ne'
  · exact (toeplitzForm_posDef_iff echoSeq_isEven n).mpr fun k _ => hE k

/-- **Uniqueness.** A sequence with nonvanishing margins is determined by `κ(0)` and its reflection data. -/
theorem evenSeq_eq_of_reflCoeff_eq {κ κ' : ℤ → ℝ} (hκ : IsEvenSeq κ) (hκ' : IsEvenSeq κ')
    (h0 : κ 0 = κ' 0) (hE : ∀ n, levinsonErr κ n ≠ 0)
    (hγ : ∀ n, reflCoeff κ n = reflCoeff κ' n) : κ = κ' := by
  have hnat : ∀ n d : ℕ, d ≤ n → κ d = κ' d := by
    intro n
    induction n with
    | zero =>
      intro d hd
      obtain rfl : d = 0 := by omega
      simpa using h0
    | succ n ih =>
      intro d hd
      rcases Nat.lt_or_ge d (n + 1) with hlt | hge
      · exact ih d (by omega)
      · obtain rfl : d = n + 1 := by omega
        have hlev := levinson_congr n ih
        have hErr : levinsonErr κ n = levinsonErr κ' n := by
          rw [levinsonErr, hlev, levinsonErr]
        have hPred : levinsonPred κ n = levinsonPred κ' n := by
          rw [levinsonPred, hlev, levinsonPred]
        have hne : levinsonErr κ' n ≠ 0 := hErr ▸ hE n
        have hβ : schurParam κ n = schurParam κ' n := by
          have h1 := hγ n
          rw [reflCoeff, reflCoeff, hErr, div_left_inj' hne] at h1
          exact h1
        rw [schurParam_eq, schurParam_eq, hPred, frozenPrediction_congr _ ih] at hβ
        have : κ ((n : ℤ) + 1) = κ' ((n : ℤ) + 1) := by linarith
        exact_mod_cast this
  funext d
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · exact hnat n n le_rfl
  · rw [hκ, hκ']
    exact hnat n n le_rfl

/-- **When is an echo train passive?** Exactly when each echo lies in its Schur band. -/
theorem passive_iff_each_echo_in_band {κ : ℤ → ℝ} (hκ : IsEvenSeq κ) :
    (∀ n, ToeplitzPosDef κ (n + 1)) ↔ 0 < κ 0 ∧ ∀ n,
      levinsonErr κ n ≠ 0 ∧ |κ ((n : ℤ) + 1) - frozenPrediction κ n (levinsonPred κ n)| < levinsonErr κ n := by
  constructor
  · intro h
    have hE : ∀ n, 0 < levinsonErr κ n := fun n => (toeplitzForm_posDef_iff hκ n).mp (h n) n le_rfl
    refine ⟨hE 0, fun n => ⟨(hE n).ne', ?_⟩⟩
    rw [← schurParam_eq]
    exact (posDef_succ_iff_abs_schur_lt hκ (h n)).mp (h (n + 1))
  · rintro ⟨h0, hband⟩ n
    have hE : ∀ n, 0 < levinsonErr κ n := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
        rw [levinsonErr_succ]
        have h1 := (hband n).2
        rw [← schurParam_eq] at h1
        have h2 : schurParam κ n ^ 2 < levinsonErr κ n ^ 2 := sq_lt_sq' (abs_lt.mp h1).1 (abs_lt.mp h1).2
        have e : levinsonErr κ n - schurParam κ n ^ 2 / levinsonErr κ n =
            (levinsonErr κ n ^ 2 - schurParam κ n ^ 2) / levinsonErr κ n := by
          field_simp
        rw [e]
        exact div_pos (by linarith) ih
    exact (toeplitzForm_posDef_iff hκ n).mpr fun k _ => hE k

/-! ### The prime dictionary -/

variable {φ : ℝ → ℝ} {r : ℝ}

theorem latticeLag_log_self (φ : ℝ → ℝ) (x : ℝ) : latticeLag φ x 1 x = ∫ u, φ u ^ 2 := by
  simp only [latticeLag, Int.cast_one, one_mul, sub_add_cancel, sq]

theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < n))

/-- **The first echo reads the prime.** At step `h = log n₀`, weights differing only at `n₀` move
the first echo by `−((λ − λ')/√n₀)‖φ‖²`. -/
theorem weilSeqW_one_sub (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hr : r < Real.log 2) {lam lam' : ℕ → ℝ}
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hlam : ∀ m : ℕ, m ≠ n₀ → lam m = lam' m) :
    weilSeqW lam φ (Real.log n₀) 1 - weilSeqW lam' φ (Real.log n₀) 1 =
      -((lam n₀ - lam' n₀) / Real.sqrt n₀) * ∫ u, φ u ^ 2 := by
  rw [weilSeqW_single_kick hφ hn₀ hlam 1, latticeLag_log_self]
  have hl := log_nat_pos hn₀
  have hl2 : Real.log 2 ≤ Real.log n₀ :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn₀)
  have h0 : latticeLag φ (Real.log n₀) 1 (-Real.log n₀) = 0 := by
    refine latticeLag_eq_zero hφ 1 ?_
    have e : -Real.log n₀ - ((1 : ℤ) : ℝ) * Real.log n₀ = -(2 * Real.log n₀) := by
      push_cast
      ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    linarith
  rw [h0, add_zero]

/-- The central datum of a short bump does not read any weight. -/
theorem weilSeqW_zero_eq_weilQuad (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hr : r < Real.log 2)
    (lam : ℕ → ℝ) (h : ℝ) : weilSeqW lam φ h 0 = weilQuad φ := by
  have hc : weilSeqW lam φ h 0 =
      weilSeqW (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) φ h 0 := by
    refine weilSeqW_congr hφ fun m hm hlog => ?_
    exfalso
    have hl2 : Real.log 2 ≤ Real.log m :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm)
    simp only [Int.cast_zero, zero_mul, abs_zero, zero_add] at hlog
    linarith
  rw [hc, weilSeqW_vonMangoldt, weilSeq, latticeTranslate_zero]
  rfl

/-- The first reflector moves by the same amount over `Q(φ)`. -/
theorem reflCoeff_zero_sub (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hr : r < Real.log 2)
    {lam lam' : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hlam : ∀ m : ℕ, m ≠ n₀ → lam m = lam' m) :
    reflCoeff (weilSeqW lam φ (Real.log n₀)) 0 - reflCoeff (weilSeqW lam' φ (Real.log n₀)) 0 =
      -((lam n₀ - lam' n₀) / Real.sqrt n₀) * (∫ u, φ u ^ 2) / weilQuad φ := by
  rw [reflCoeff_zero_eq, reflCoeff_zero_eq, weilSeqW_zero_eq_weilQuad hφ hr,
    weilSeqW_zero_eq_weilQuad hφ hr, ← sub_div, weilSeqW_one_sub hφ hr hn₀ hlam]

/-- **`Λ(n₀)` from the first reflector.** With `λ'` the von Mangoldt weight with `n₀` removed,
`Λ(n₀) = √n₀ (κ^{λ'}(1) − γ₀Q(φ))/‖φ‖²` at step `log n₀`. -/
theorem vonMangoldt_eq_of_reflCoeff (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hr : r < Real.log 2)
    (hQ : 0 < weilQuad φ) (hnorm : 0 < ∫ u, φ u ^ 2) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    (ArithmeticFunction.vonMangoldt n₀ : ℝ) =
      Real.sqrt n₀ * (weilSeqW (Function.update (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n₀ 0)
          φ (Real.log n₀) 1 -
        reflCoeff (weilSeq φ (Real.log n₀)) 0 * weilQuad φ) / ∫ u, φ u ^ 2 := by
  set L : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) with hL
  set L' := Function.update L n₀ 0 with hL'
  have hkick := weilSeqW_one_sub hφ hr (lam := L) (lam' := L') hn₀ fun m hm => by
    rw [hL', Function.update_of_ne hm]
  have hγ : reflCoeff (weilSeq φ (Real.log n₀)) 0 * weilQuad φ = weilSeqW L φ (Real.log n₀) 1 := by
    rw [← weilSeqW_vonMangoldt, reflCoeff_zero_eq, weilSeqW_zero_eq_weilQuad hφ hr]
    exact div_mul_cancel₀ _ hQ.ne'
  rw [hγ]
  have hs : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have e : L' n₀ = 0 := by rw [hL', Function.update_self]
  rw [e, sub_zero] at hkick
  have hd : weilSeqW L' φ (Real.log n₀) 1 - weilSeqW L φ (Real.log n₀) 1 =
      (L n₀ / Real.sqrt n₀) * ∫ u, φ u ^ 2 := by linarith
  rw [hd]
  field_simp
  rfl

/-- A short bump exists at every scale. -/
theorem exists_short_bump {r : ℝ} (hr : 0 < r) :
    ∃ φ ∈ realTests, φ ≠ 0 ∧ (∀ y, y ∉ Icc (-r) 0 → φ y = 0) ∧ 0 < ∫ u, φ u ^ 2 := by
  let b : ContDiffBump (-r / 2 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsm : ContDiff ℝ 2 (b : ℝ → ℝ) := b.contDiff
  have hcs : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hone : (b : ℝ → ℝ) (-r / 2) = 1 := b.one_of_mem_closedBall (by simp; positivity)
  refine ⟨b, ⟨hsm, hcs⟩, fun h0 => ?_, fun y hy => ?_, ?_⟩
  · have := congrFun h0 (-r / 2)
    rw [hone] at this
    simp at this
  · refine b.zero_of_le_dist ?_
    simp only [Real.dist_eq, Set.mem_Icc, not_and_or, not_le] at hy ⊢
    change r / 2 ≤ _
    rcases hy with hy | hy
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  · exact (hsm.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)) (fun _ => sq_nonneg _)
      (x := -r / 2) (by rw [hone]; norm_num)

/-- **The reflection data determine the prime weights.** Two weights with equal first reflectors on every
short bump and every step agree at every `n ≥ 2`. -/
theorem weight_eq_of_reflCoeff_eq {lam lam' : ℕ → ℝ}
    (h : ∀ φ ∈ realTests, φ ≠ 0 → (∀ y, y ∉ Icc (-(Real.log 2 / 2)) 0 → φ y = 0 ) → ∀ h : ℝ, 0 < h →
      reflCoeff (weilSeqW lam φ h) 0 = reflCoeff (weilSeqW lam' φ h) 0)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : lam n₀ = lam' n₀ := by
  -- a window of radius below the gaps of `log` around `n₀`
  have hn0 : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
  have hup : 0 < Real.log ((n₀ : ℝ) + 1) - Real.log n₀ :=
    sub_pos.mpr (Real.log_lt_log hn0 (by linarith))
  have hn1 : (0 : ℝ) < (n₀ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  have hdown : 0 < Real.log n₀ - Real.log ((n₀ : ℝ) - 1) :=
    sub_pos.mpr (Real.log_lt_log hn1 (by linarith))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := min (Real.log 2 / 2) (min ((Real.log ((n₀ : ℝ) + 1) - Real.log n₀) / 2)
    ((Real.log n₀ - Real.log ((n₀ : ℝ) - 1)) / 2)) with hrdef
  have hr0 : 0 < r := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hr1 : r ≤ Real.log 2 / 2 := min_le_left _ _
  have hr2 : r ≤ (Real.log ((n₀ : ℝ) + 1) - Real.log n₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (Real.log n₀ - Real.log ((n₀ : ℝ) - 1)) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨φ, hφ, hφ0, hsupp, hnorm⟩ := exists_short_bump hr0
  have hshort : ∀ y, y ∉ Icc (-(Real.log 2 / 2)) 0 → φ y = 0 := fun y hy => hsupp y fun hmem =>
    hy ⟨by linarith [hmem.1], hmem.2⟩
  have hlt : r < Real.log 2 := by linarith
  have hQ : 0 < weilQuad φ := by
    refine weilQuad_pos_of_short hφ hφ0 (c := 0) (L := r) ?_ (fun u hu => hsupp u (by simpa using hu))
    have : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hlog : 0 < Real.log n₀ := log_nat_pos hn₀
  have hγ := h φ hφ hφ0 hshort (Real.log n₀) hlog
  rw [reflCoeff_zero_eq, reflCoeff_zero_eq, weilSeqW_zero_eq_weilQuad hsupp hlt,
    weilSeqW_zero_eq_weilQuad hsupp hlt, div_left_inj' hQ.ne'] at hγ
  -- only `n₀` is seen at the first site
  set lam'' := Function.update lam' n₀ (lam n₀) with hlam''
  have hsee : weilSeqW lam φ (Real.log n₀) 1 = weilSeqW lam'' φ (Real.log n₀) 1 := by
    unfold weilSeqW
    rw [weilFullFunctional_congr_of_vanish (lam' := lam'') fun m hm hne => ?_]
    have hmn : m ≠ n₀ := by
      rintro rfl
      exact hne (by rw [hlam'', Function.update_self])
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hml := log_nat_pos hm
    have hgap : r < |Real.log m - ((1 : ℤ) : ℝ) * Real.log n₀| := by
      rcases Nat.lt_or_gt_of_ne hmn with hlt' | hgt'
      · have hle : (m : ℝ) ≤ (n₀ : ℝ) - 1 := by
          have : (m : ℝ) + 1 ≤ n₀ := by exact_mod_cast hlt'
          linarith
        have := Real.log_le_log hm0 hle
        rw [Int.cast_one, one_mul, abs_of_neg (by linarith)]
        linarith
      · have hle : (n₀ : ℝ) + 1 ≤ m := by exact_mod_cast hgt'
        have := Real.log_le_log (by linarith) hle
        rw [Int.cast_one, one_mul, abs_of_pos (by linarith)]
        linarith
    have hgap2 : r < |-Real.log m - ((1 : ℤ) : ℝ) * Real.log n₀| := by
      have e : -Real.log m - ((1 : ℤ) : ℝ) * Real.log n₀ = -(Real.log m + Real.log n₀) := by
        push_cast
        ring
      rw [e, abs_neg, abs_of_pos (by linarith)]
      have : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm)
      linarith
    rw [weilTest_latticeTranslate, weilTest_latticeTranslate, latticeLag_eq_zero hsupp 1 hgap,
      latticeLag_eq_zero hsupp 1 hgap2]
    simp
  have hkick := weilSeqW_one_sub hsupp hlt (lam := lam'') (lam' := lam') hn₀ fun m hm => by
    rw [hlam'', Function.update_of_ne hm]
  rw [← hsee, hγ, sub_self] at hkick
  have e : lam'' n₀ = lam n₀ := by rw [hlam'', Function.update_self]
  rw [e] at hkick
  have hs : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr hn0
  have hz := mul_eq_zero.mp hkick.symm
  rcases hz with hz | hz
  · have h3 : (lam n₀ - lam' n₀) / Real.sqrt n₀ = 0 := by linarith
    rcases div_eq_zero_iff.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hs.ne'
  · exact absurd hz hnorm.ne'

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
