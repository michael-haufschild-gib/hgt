import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsDeterminedByItsValuesOnWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheContactsOfFlatPacketsAreTheirOverlapLengths
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleIsDecidedOnBlockAverages

/-!
# On nested windows the comb form tends to Weil's form of the step packet

Weil's form on the comb at finite scale (`HodgeTheoryOfAFixedPart.combForm`) is evaluated on
the divisors that are combinations of the flat divisors of nested windows `(x₀N, x_jN]`, the
divisors that are constant on blocks. Per degree point of the scale it tends to Weil's form
`𝔚_Q` of the step packet `Σ τ_j flatPacket x₀ x_j`, uniformly on the unit sphere of the
coefficients.

* **One window** (`combForm_window_eq`, `tendsto_combForm_window_div`). On the flat divisor of
  `(aN, bN]` the form is the pole term `2(H_{bN} − H_{aN})(b − a)N`, minus the energy of the
  jets with its counterterm, minus twice the contacts; the contacts of ratio `k` are `Λ(k)`
  times the number of `m` in the window with `km` in the window
  (`sum_sum_contact_window`). Over `N` it tends to `𝔚_Q(flatPacket a b)`.
* **The form is a quadratic form** (`polarOn_combForm`): the polar identity on every family of
  divisors, from the bilinear form of the continuation.
* **Nested windows** (`tendsto_combForm_nested_div`, `eventually_abs_combForm_nested_sub_le`).
  Both sides satisfy the polar identity, and a difference of two nested flat divisors is the
  flat divisor of the window between their ends, up to sign. So the limit holds on every
  combination, with an error at most `η Σ τ_j²` for all coefficients at once.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (degOne degTwo combPairing combBilin formBilin pairKernel contact
  counterterm flatContactPoints)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### The polar identity of a biadditive function -/

section Biadditive

variable {α ι : Type*}

/-- The diagonal of a function that is additive and homogeneous in each argument satisfies the
polar identity on every finite family. -/
theorem polarOn_of_biadditive (B : (α → ℝ) → (α → ℝ) → ℝ)
    (hla : ∀ c c' e, B (fun n => c n + c' n) e = B c e + B c' e)
    (hls : ∀ (t : ℝ) c e, B (fun n => t * c n) e = t * B c e)
    (hra : ∀ c e e', B c (fun n => e n + e' n) = B c e + B c e')
    (hrs : ∀ (t : ℝ) c e, B c (fun n => t * e n) = t * B c e)
    (v : ι → α → ℝ) (s : Finset ι) : PolarOn (fun c => B c c) v s := by
  classical
  have hl0 : ∀ e, B (fun _ => 0) e = 0 := fun e => by
    have h := hls 0 (fun _ => 0) e
    simpa using h
  have hr0 : ∀ c, B c (fun _ => 0) = 0 := fun c => by
    have h := hrs 0 c (fun _ => 0)
    simpa using h
  have hlsum : ∀ (t : Finset ι) (τ : ι → ℝ) (e : α → ℝ),
      B (fun n => ∑ j ∈ t, τ j * v j n) e = ∑ j ∈ t, τ j * B (v j) e := by
    intro t τ e
    induction t using Finset.induction_on with
    | empty => simpa using hl0 e
    | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [hla, hls, ih]
  have hrsum : ∀ (t : Finset ι) (τ : ι → ℝ) (c : α → ℝ),
      B c (fun n => ∑ j ∈ t, τ j * v j n) = ∑ j ∈ t, τ j * B c (v j) := by
    intro t τ c
    induction t using Finset.induction_on with
    | empty => simpa using hr0 c
    | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [hra, hrs, ih]
  refine polarOn_of_bilin (fun j l => B (v j) (v l)) ?_ ?_ (fun _ _ => rfl)
  · intro τ
    beta_reduce
    rw [hlsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · intro j _ l _
    beta_reduce
    have e : (fun u => v l u - v j u) = fun u => v l u + (-1) * v j u := by
      funext u
      ring
    have h1 : B (fun u => v l u + (-1) * v j u) (fun u => v l u + (-1) * v j u) =
        B (v l) (fun u => v l u + (-1) * v j u) +
          (-1) * B (v j) (fun u => v l u + (-1) * v j u) := by
      rw [hla (v l) (fun u => (-1) * v j u), hls (-1) (v j)]
    have h2 : ∀ c : α → ℝ, B c (fun u => v l u + (-1) * v j u) =
        B c (v l) + (-1) * B c (v j) := fun c => by
      rw [hra c (v l) (fun u => (-1) * v j u), hrs (-1) c (v j)]
    rw [e, h1, h2, h2]
    ring

end Biadditive

/-! ### Weil's form on the comb is a quadratic form -/

section FormBilin

variable (S : Finset ℕ)

theorem formBilin_add_left (c c' e : ℕ → ℝ) :
    formBilin S (fun n => c n + c' n) e = formBilin S c e + formBilin S c' e := by
  have h1 : degOne S (fun n => c n + c' n) = degOne S c + degOne S c' := by
    simp only [degOne, add_div, Finset.sum_add_distrib]
  have h2 : degTwo S (fun n => c n + c' n) = degTwo S c + degTwo S c' := by
    simp only [degTwo, Finset.sum_add_distrib]
  have h3 : combBilin S (fun n => c n + c' n) e = combBilin S c e + combBilin S c' e := by
    simp only [combBilin, add_mul, Finset.sum_add_distrib]
    ring
  rw [formBilin, formBilin, formBilin, h1, h2, h3]
  ring

theorem formBilin_const_mul_left (t : ℝ) (c e : ℕ → ℝ) :
    formBilin S (fun n => t * c n) e = t * formBilin S c e := by
  have h1 : degOne S (fun n => t * c n) = t * degOne S c := by
    simp only [degOne, Finset.mul_sum, mul_div_assoc]
  have h2 : degTwo S (fun n => t * c n) = t * degTwo S c := by
    simp only [degTwo, Finset.mul_sum]
  have h3 : combBilin S (fun n => t * c n) e = t * combBilin S c e := by
    simp only [combBilin, mul_sub, Finset.mul_sum]
    exact congrArg₂ (· - ·)
      (Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring)
      (Finset.sum_congr rfl fun n _ => by ring)
  rw [formBilin, formBilin, h1, h2, h3]
  ring

theorem formBilin_comm (c e : ℕ → ℝ) : formBilin S c e = formBilin S e c := by
  rw [formBilin, formBilin, HodgeTheoryOfAFixedPart.combBilin_comm S c e]
  ring

theorem formBilin_add_right (c e e' : ℕ → ℝ) :
    formBilin S c (fun n => e n + e' n) = formBilin S c e + formBilin S c e' := by
  rw [formBilin_comm, formBilin_add_left, formBilin_comm S e, formBilin_comm S e']

theorem formBilin_const_mul_right (t : ℝ) (c e : ℕ → ℝ) :
    formBilin S c (fun n => t * e n) = t * formBilin S c e := by
  rw [formBilin_comm, formBilin_const_mul_left, formBilin_comm S e]

/-- **Weil's form on the comb satisfies the polar identity** on every family of divisors. -/
theorem polarOn_combForm {ι : Type*} (v : ι → ℕ → ℝ) (s : Finset ι) :
    PolarOn (combW S) v s := by
  have h := polarOn_of_biadditive (formBilin S) (formBilin_add_left S)
    (formBilin_const_mul_left S) (formBilin_add_right S) (formBilin_const_mul_right S) v s
  intro τ
  have hτ := h τ
  simp only [HodgeTheoryOfAFixedPart.formBilin_self] at hτ
  exact hτ

/-- The form does not see the sign of a divisor. -/
theorem combForm_neg_fun (c : ℕ → ℝ) : combW S (fun n => -c n) = combW S c := by
  have e : (fun n => -c n) = fun n => (-1) * c n := by
    funext n
    ring
  rw [← HodgeTheoryOfAFixedPart.formBilin_self S (fun n => -c n),
    ← HodgeTheoryOfAFixedPart.formBilin_self S c, e, formBilin_const_mul_left,
    formBilin_const_mul_right]
  ring

end FormBilin

/-! ### Support and congruence -/

section Support

variable {S W : Finset ℕ} {c c' : ℕ → ℝ}

theorem combForm_congr (h : ∀ n ∈ S, c n = c' n) : combW S c = combW S c' := by
  have h1 : degOne S c = degOne S c' := Finset.sum_congr rfl fun n hn => by rw [h n hn]
  have h2 : degTwo S c = degTwo S c' := Finset.sum_congr rfl fun n hn => h n hn
  have h3 : combPairing S c = combPairing S c' := by
    unfold HodgeTheoryOfAFixedPart.combPairing
    refine congrArg₂ (· - ·)
      (Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_)
      (Finset.sum_congr rfl fun n hn => by rw [h n hn])
    rw [h n hn, h m (Finset.mem_of_mem_erase hm)]
  rw [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combForm, h1, h2, h3]

/-- A divisor that vanishes off `W ⊆ S` has the same form on `S` and on `W`. -/
theorem combForm_of_subset (hWS : W ⊆ S) (h0 : ∀ n ∈ S, n ∉ W → c n = 0) :
    combW S c = combW W c := by
  have h1 : degOne S c = degOne W c :=
    (Finset.sum_subset hWS fun n hn hnW => by rw [h0 n hn hnW, zero_div]).symm
  have h2 : degTwo S c = degTwo W c :=
    (Finset.sum_subset hWS fun n hn hnW => h0 n hn hnW).symm
  have h3 : combPairing S c = combPairing W c := by
    unfold HodgeTheoryOfAFixedPart.combPairing
    have hout : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * pairKernel m n =
        ∑ n ∈ W, ∑ m ∈ S.erase n, c m * c n * pairKernel m n :=
      (Finset.sum_subset hWS fun n hn hnW => Finset.sum_eq_zero fun m _ => by
        rw [h0 n hn hnW]
        ring).symm
    have hin : ∀ n ∈ W, ∑ m ∈ S.erase n, c m * c n * pairKernel m n =
        ∑ m ∈ W.erase n, c m * c n * pairKernel m n := fun n _ =>
      (Finset.sum_subset (Finset.erase_subset_erase n hWS) fun m hm hmW => by
        have hmS : m ∈ S := Finset.mem_of_mem_erase hm
        have hmW' : m ∉ W := fun h =>
          hmW (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hm).1, h⟩)
        rw [h0 m hmS hmW']
        ring).symm
    have hct : ∑ n ∈ S, c n ^ 2 * counterterm n = ∑ n ∈ W, c n ^ 2 * counterterm n :=
      (Finset.sum_subset hWS fun n hn hnW => by
        rw [h0 n hn hnW]
        ring).symm
    rw [hout, Finset.sum_congr rfl hin, hct]
  rw [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combForm, h1, h2, h3]

end Support

/-! ### The flat divisor of a window -/

/-- The flat divisor of the window `(A, B]`: `1` on its degree points. -/
def windowDivisor (A B n : ℕ) : ℝ := if n ∈ Ioc A B then 1 else 0

theorem windowDivisor_of_mem {A B n : ℕ} (h : n ∈ Ioc A B) : windowDivisor A B n = 1 := if_pos h

theorem windowDivisor_of_notMem {A B n : ℕ} (h : n ∉ Ioc A B) : windowDivisor A B n = 0 :=
  if_neg h

/-- Nested flat divisors differ by the flat divisor of the window between their ends. -/
theorem windowDivisor_sub {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (n : ℕ) :
    windowDivisor A C n - windowDivisor A B n = windowDivisor B C n := by
  simp only [windowDivisor, Finset.mem_Ioc]
  by_cases h1 : n ≤ B
  · rw [if_neg (fun h : B < n ∧ n ≤ C => absurd h.1 (not_lt.mpr h1))]
    by_cases h2 : A < n
    · rw [if_pos ⟨h2, h1.trans hBC⟩, if_pos ⟨h2, h1⟩, sub_self]
    · rw [if_neg (fun h : A < n ∧ n ≤ C => h2 h.1), if_neg (fun h : A < n ∧ n ≤ B => h2 h.1),
        sub_zero]
  · have hBn : B < n := lt_of_not_ge h1
    rw [if_neg (fun h : A < n ∧ n ≤ B => h1 h.2)]
    by_cases h2 : n ≤ C
    · rw [if_pos ⟨lt_of_le_of_lt hAB hBn, h2⟩, if_pos ⟨hBn, h2⟩, sub_zero]
    · rw [if_neg (fun h : A < n ∧ n ≤ C => h2 h.2), if_neg (fun h : B < n ∧ n ≤ C => h2 h.2),
        sub_zero]

theorem combForm_windowDivisor {S : Finset ℕ} {A B : ℕ} (hS : Ioc A B ⊆ S) :
    combW S (windowDivisor A B) = combW (Ioc A B) (fun _ => 1) :=
  (combForm_of_subset hS fun n _ hn => windowDivisor_of_notMem hn).trans
    (combForm_congr fun n hn => windowDivisor_of_mem hn)

/-! ### One window at finite scale -/

theorem sum_Ioc_one_div {A B : ℕ} (hAB : A ≤ B) :
    ∑ n ∈ Ioc A B, 1 / (n : ℝ) = harm B - harm A := by
  have hI : ∀ N : ℕ, Icc 1 N = Ioc 0 N := fun N => by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← HodgeTheoryOfAFixedPart.sum_Icc_one_div B, ← HodgeTheoryOfAFixedPart.sum_Icc_one_div A,
    hI, hI, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le A) hAB]
  ring

/-- **The contacts inside a window.** A contact of ratio `k` joins `m` and `km`, both in the
window; ratios beyond `Q` do not occur when `B ≤ Q A`. -/
theorem sum_sum_contact_window {A B Q : ℕ} (hQ : B ≤ Q * A) :
    ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, contact m n =
      2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        (((Ioc A B).filter fun m => k * m ∈ Ioc A B).card : ℝ) := by
  -- the contacts directed upwards, with the diagonal added
  have hdir1 : ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n,
        (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ n ∈ Ioc A B, ∑ m ∈ Ioc A B, if m ∣ n then (Λ (n / m) : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun n hn => Finset.sum_erase _ ?_
    have hn0 : 0 < n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    rw [if_pos (dvd_refl n), Nat.div_self hn0, ArithmeticFunction.vonMangoldt_apply_one]
  have hdir2 : ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n,
        (if n ∣ m then (Λ (m / n) : ℝ) else 0) =
      ∑ n ∈ Ioc A B, ∑ m ∈ Ioc A B, if m ∣ n then (Λ (n / m) : ℝ) else 0 := by
    rw [HodgeTheoryOfAFixedPart.sum_erase_comm (Ioc A B)
      fun m n => if n ∣ m then (Λ (m / n) : ℝ) else 0]
    exact hdir1
  have hsplit : ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, contact m n =
      (∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, (if m ∣ n then (Λ (n / m) : ℝ) else 0)) +
        ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, (if n ∣ m then (Λ (m / n) : ℝ) else 0) := by
    simp only [HodgeTheoryOfAFixedPart.contact, Finset.sum_add_distrib]
  -- reindex by the ratio
  have hinner : ∀ m ∈ Ioc A B, ∑ n ∈ Ioc A B, (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ k ∈ Icc 1 Q, if k * m ∈ Ioc A B then (Λ k : ℝ) else 0 := by
    intro m hm
    have hAm : A < m := (Finset.mem_Ioc.mp hm).1
    have hm0 : 0 < m := by omega
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij' (fun n _ => n / m) (fun k _ => k * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnW, hdvd⟩ := Finset.mem_filter.mp hn
      have hnB : n ≤ B := (Finset.mem_Ioc.mp hnW).2
      have hn0 : 0 < n := by
        have := (Finset.mem_Ioc.mp hnW).1
        omega
      have hkm : n / m * m = n := Nat.div_mul_cancel hdvd
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdvd) hm0, ?_⟩, by rw [hkm]; exact hnW⟩
      by_contra hlt
      have hQk : Q + 1 ≤ n / m := by omega
      have h1 : (Q + 1) * m ≤ n := (Nat.mul_le_mul_right m hQk).trans_eq hkm
      have h2 : Q * A ≤ Q * m := Nat.mul_le_mul_left Q hAm.le
      nlinarith
    · intro k hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).2, Dvd.intro_left k rfl⟩
    · intro n hn
      exact Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    · intro k _
      exact Nat.mul_div_cancel k hm0
    · intro n _
      rfl
  have hcount : ∀ k ∈ Icc 1 Q, ∑ m ∈ Ioc A B, (if k * m ∈ Ioc A B then (Λ k : ℝ) else 0) =
      (Λ k : ℝ) * (((Ioc A B).filter fun m => k * m ∈ Ioc A B).card : ℝ) := fun k _ => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hD : ∑ n ∈ Ioc A B, ∑ m ∈ Ioc A B, (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * (((Ioc A B).filter fun m => k * m ∈ Ioc A B).card : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_comm,
      Finset.sum_congr rfl hcount]
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun k hk hk2 => ?_).symm
    have hk1 : k = 1 := by
      have h1 := (Finset.mem_Icc.mp hk).1
      have h2 := (Finset.mem_Icc.mp hk).2
      by_contra hne
      exact hk2 (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
    rw [hk1, ArithmeticFunction.vonMangoldt_apply_one, zero_mul]
  rw [hsplit, hdir1, hdir2, hD]
  ring

/-- **Weil's form of the flat divisor of a window.** -/
theorem combForm_window_eq {A B Q : ℕ} (hAB : A ≤ B) (hQ : B ≤ Q * A) :
    combW (Ioc A B) (fun _ => 1) =
      2 * ((harm B - harm A) * ((B : ℝ) - A)) -
        ((windowEnergy A B - ∑ n ∈ Ioc A B, Real.log ((n : ℝ) / (2 * Real.pi))) +
          2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
            (((Ioc A B).filter fun m => k * m ∈ Ioc A B).card : ℝ)) := by
  have h1 : degOne (Ioc A B) (fun _ => (1 : ℝ)) = harm B - harm A := by
    rw [HodgeTheoryOfAFixedPart.degOne]
    exact sum_Ioc_one_div hAB
  have h2 : degTwo (Ioc A B) (fun _ => (1 : ℝ)) = (B : ℝ) - A := by
    rw [HodgeTheoryOfAFixedPart.degTwo, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
      Nat.cast_sub hAB]
  have h3 : combPairing (Ioc A B) (fun _ => (1 : ℝ)) =
      windowEnergy A B + ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, contact m n -
        ∑ n ∈ Ioc A B, Real.log ((n : ℝ) / (2 * Real.pi)) := by
    unfold HodgeTheoryOfAFixedPart.combPairing windowEnergy
    rw [← Finset.sum_add_distrib]
    refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun n _ => ?_)
      (Finset.sum_congr rfl fun n _ => ?_)
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by
        rw [HodgeTheoryOfAFixedPart.pairKernel]
        ring
    · rw [HodgeTheoryOfAFixedPart.counterterm]
      ring
  rw [HodgeTheoryOfAFixedPart.combForm, h1, h2, h3, sum_sum_contact_window hQ]
  ring

/-! ### One window in the limit -/

theorem packetForm_zero (Q : ℕ) : packetForm Q (fun _ => 0) = 0 := by
  simp [packetForm, packetAutocorr, levyJump]

theorem flatPacket_self (a : ℝ) : flatPacket a a = fun _ => 0 := by
  funext u
  simp [flatPacket]

theorem tendsto_harm_mul_sub {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => harm (b * N) - harm (a * N)) atTop
      (𝓝 (Real.log b - Real.log a)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := ha'.trans_le (by exact_mod_cast hab)
  have hb1 : Tendsto (fun N : ℕ => b * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (ha.trans hab)) tendsto_id
  have ha1 : Tendsto (fun N : ℕ => a * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N ha) tendsto_id
  have h := ((tendsto_harm_sub_log.comp hb1).sub (tendsto_harm_sub_log.comp ha1)).add_const
    (Real.log b - Real.log a)
  rw [sub_self, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply, Nat.cast_mul]
  rw [Real.log_mul hb'.ne' hN'.ne', Real.log_mul ha'.ne' hN'.ne']
  ring

/-- **One window.** For naturals `1 ≤ a ≤ b ≤ Q a`, Weil's form of the flat divisor of
`(aN, bN]`, per degree point of the scale, tends to Weil's form of the flat packet. -/
theorem tendsto_combForm_window_div {a b Q : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hQ : b ≤ Q * a) :
    Tendsto (fun N : ℕ => combW (Ioc (a * N) (b * N)) (fun _ => 1) / N) atTop
      (𝓝 (packetForm Q (flatPacket a b))) := by
  rcases hab.eq_or_lt with rfl | hlt
  · have h0 : ∀ N : ℕ, combW (Ioc (a * N) (a * N)) (fun _ => (1 : ℝ)) / N = 0 := fun N => by
      rw [Finset.Ioc_self]
      simp [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combPairing,
        HodgeTheoryOfAFixedPart.degOne, HodgeTheoryOfAFixedPart.degTwo]
    rw [flatPacket_self, packetForm_zero]
    exact tendsto_const_nhds.congr fun N => (h0 N).symm
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hjets := tendsto_windowEnergy_jumpForm ha hlt
  have hfilt : ∀ (k N : ℕ), ((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)) =
      flatContactPoints a b a b k N := fun k N => by
    unfold HodgeTheoryOfAFixedPart.flatContactPoints
    exact Finset.filter_congr fun m _ => Finset.mem_Ioc
  have hcont : Tendsto (fun N : ℕ => ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
      ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N))
      atTop (𝓝 (∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        (packetAutocorr (flatPacket a b) (Real.log k) / Real.exp (Real.log k / 2)))) :=
    tendsto_finsetSum _ fun k hk => by
      have hk1 : 1 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      have h := (HodgeTheoryOfAFixedPart.tendsto_flatContactPoints_self_autocorr ha hab hk1).const_mul
        (Λ k : ℝ)
      exact h.congr fun N => by rw [hfilt k N]
  have hmain := (((tendsto_harm_mul_sub ha hab).mul
    (tendsto_const_nhds (x := (b : ℝ) - a))).const_mul 2).sub (hjets.add (hcont.const_mul 2))
  have hval : 2 * ((Real.log b - Real.log a) * ((b : ℝ) - a)) -
      (-(EF.gammaBracket 0 * packetAutocorr (flatPacket a b) 0 +
          ∫ x in Set.Ioi 0, levyJump (flatPacket a b) x) +
        2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
          (packetAutocorr (flatPacket a b) (Real.log k) / Real.exp (Real.log k / 2))) =
      packetForm Q (flatPacket a b) := by
    have hsum : ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        (packetAutocorr (flatPacket a b) (Real.log k) / Real.exp (Real.log k / 2)) =
        ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr (flatPacket a b) (Real.log k) :=
      Finset.sum_congr rfl fun k hk => by
        have hk0 : (0 : ℝ) < k := by
          have := (Finset.mem_Icc.mp hk).1
          exact_mod_cast (by omega : 0 < k)
        rw [contactWeight, Real.exp_half, Real.exp_log hk0]
        ring
    rw [packetForm, integral_flatPacket_mul_exp_neg ha' hab', integral_flatPacket_mul_exp ha' hab',
      hsum]
    ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hsumdiv : ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
      ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N) =
      (∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        (((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [combForm_window_eq (Nat.mul_le_mul_right N hab)
    ((Nat.mul_le_mul_right N hQ).trans_eq (Nat.mul_assoc Q a N)), hsumdiv]
  push_cast
  field_simp
  ring

/-! ### Nested windows -/

section Nested

variable {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X Q : ℕ}

/-- The difference of two nested flat divisors on a window that contains both. -/
theorem combForm_windowDivisor_sub {y z N : ℕ} (hy : x₀ ≤ y) (hyX : y ≤ X) (hz : x₀ ≤ z)
    (hzX : z ≤ X) :
    combW (Ioc (x₀ * N) (X * N))
        (fun n => windowDivisor (x₀ * N) (z * N) n - windowDivisor (x₀ * N) (y * N) n) =
      combW (Ioc (min y z * N) (max y z * N)) (fun _ => 1) := by
  have hsub : ∀ {p r : ℕ}, x₀ ≤ p → r ≤ X → Ioc (p * N) (r * N) ⊆ Ioc (x₀ * N) (X * N) :=
    fun hp hr => Finset.Ioc_subset_Ioc (Nat.mul_le_mul_right N hp) (Nat.mul_le_mul_right N hr)
  rcases le_total y z with h | h
  · rw [min_eq_left h, max_eq_right h]
    have e : (fun n => windowDivisor (x₀ * N) (z * N) n - windowDivisor (x₀ * N) (y * N) n) =
        windowDivisor (y * N) (z * N) := by
      funext n
      exact windowDivisor_sub (Nat.mul_le_mul_right N hy) (Nat.mul_le_mul_right N h) n
    rw [e]
    exact combForm_windowDivisor (hsub hy hzX)
  · rw [min_eq_right h, max_eq_left h]
    have e : (fun n => windowDivisor (x₀ * N) (z * N) n - windowDivisor (x₀ * N) (y * N) n) =
        fun n => -windowDivisor (z * N) (y * N) n := by
      funext n
      rw [← windowDivisor_sub (Nat.mul_le_mul_right N hz) (Nat.mul_le_mul_right N h) n, neg_sub]
    rw [e, combForm_neg_fun]
    exact combForm_windowDivisor (hsub hz hyX)

/-- The entry of the form at finite scale: the polar combination of three windows. -/
def nestedEntry (x₀ : ℕ) (x : ι → ℕ) (N : ℕ) (j l : ι) : ℝ :=
  (combW (Ioc (x₀ * N) (x j * N)) (fun _ => 1) + combW (Ioc (x₀ * N) (x l * N)) (fun _ => 1) -
    combW (Ioc (min (x j) (x l) * N) (max (x j) (x l) * N)) (fun _ => 1)) / N

/-- The entry of the limit form. -/
def stepEntry (Q x₀ : ℕ) (x : ι → ℕ) (j l : ι) : ℝ :=
  packetForm Q (flatPacket x₀ (x j)) + packetForm Q (flatPacket x₀ (x l)) -
    packetForm Q (flatPacket (min (x j) (x l) : ℕ) (max (x j) (x l) : ℕ))

theorem tendsto_nestedEntry (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X)
    (hQ : X ≤ Q * x₀) {j l : ι} (hj : j ∈ s) (hl : l ∈ s) :
    Tendsto (fun N : ℕ => nestedEntry x₀ x N j l) atTop (𝓝 (stepEntry Q x₀ x j l)) := by
  have hmin : x₀ ≤ min (x j) (x l) := le_min (hx j hj).1 (hx l hl).1
  have hmax : max (x j) (x l) ≤ X := max_le (hx j hj).2 (hx l hl).2
  have h1 := tendsto_combForm_window_div hx₀ (hx j hj).1 ((hx j hj).2.trans hQ)
  have h2 := tendsto_combForm_window_div hx₀ (hx l hl).1 ((hx l hl).2.trans hQ)
  have h3 := tendsto_combForm_window_div (Q := Q) (hx₀.trans hmin) min_le_max
    (hmax.trans (hQ.trans (Nat.mul_le_mul_left Q hmin)))
  refine ((h1.add h2).sub h3).congr fun N => ?_
  rw [nestedEntry]
  ring

/-- Weil's form at finite scale on a combination of nested flat divisors, through the
entries. -/
theorem combForm_nested_eq (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (τ : ι → ℝ) (N : ℕ) :
    combW (Ioc (x₀ * N) (X * N)) (fun n => ∑ j ∈ s, τ j * windowDivisor (x₀ * N) (x j * N) n) / N =
      1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * nestedEntry x₀ x N j l := by
  have hp := polarOn_combForm (Ioc (x₀ * N) (X * N))
    (fun j => windowDivisor (x₀ * N) (x j * N)) s τ
  rw [hp, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hsub : ∀ i ∈ s, Ioc (x₀ * N) (x i * N) ⊆ Ioc (x₀ * N) (X * N) := fun i hi =>
    Finset.Ioc_subset_Ioc le_rfl (Nat.mul_le_mul_right N (hx i hi).2)
  rw [combForm_windowDivisor (hsub j hj), combForm_windowDivisor (hsub l hl),
    combForm_windowDivisor_sub (hx j hj).1 (hx j hj).2 (hx l hl).1 (hx l hl).2, nestedEntry]
  ring

/-- Weil's form of the step packet through the entries. -/
theorem packetForm_nested_eq (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (τ : ι → ℝ) :
    packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) =
      1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * stepEntry Q x₀ x j l := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hxr : ∀ j ∈ s, (x₀ : ℝ) ≤ ((x j : ℕ) : ℝ) := fun j hj => by exact_mod_cast (hx j hj).1
  have hp := polarOn_packetForm_flatPacket (s := s) (x := fun j => ((x j : ℕ) : ℝ)) Q hx₀' hxr τ
  rw [hp]
  congr 1
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
  rw [packetForm_flatPacket_sub_flatPacket Q hx₀' (hxr j hj) (hxr l hl), stepEntry,
    Nat.cast_min, Nat.cast_max]

/-- **Limit matrices.** On the combinations of the flat divisors of nested windows, Weil's form
on the comb, per degree point of the scale, tends to Weil's form of the step packet. -/
theorem tendsto_combForm_nested_div (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X)
    (hQ : X ≤ Q * x₀) (τ : ι → ℝ) :
    Tendsto (fun N : ℕ => combW (Ioc (x₀ * N) (X * N))
        (fun n => ∑ j ∈ s, τ j * windowDivisor (x₀ * N) (x j * N) n) / N) atTop
      (𝓝 (packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u))) := by
  rw [packetForm_nested_eq hx₀ hx τ]
  have h : Tendsto (fun N : ℕ => 1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * nestedEntry x₀ x N j l)
      atTop (𝓝 (1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * stepEntry Q x₀ x j l)) :=
    (tendsto_finsetSum _ fun j hj => tendsto_finsetSum _ fun l hl =>
      (tendsto_nestedEntry hx₀ hx hQ hj hl).const_mul (τ j * τ l)).const_mul _
  exact h.congr fun N => (combForm_nested_eq hx τ N).symm

/-- A double sum against entries of size at most `δ`. -/
theorem abs_half_sum_sum_le (τ : ι → ℝ) (d : ι → ι → ℝ) {δ : ℝ}
    (hd : ∀ j ∈ s, ∀ l ∈ s, |d j l| ≤ δ) :
    |1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * d j l| ≤ δ / 2 * (s.card * ∑ j ∈ s, τ j ^ 2) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hd j₀ hj₀ j₀ hj₀)
  have h1 : |∑ j ∈ s, ∑ l ∈ s, τ j * τ l * d j l| ≤ ∑ j ∈ s, ∑ l ∈ s, |τ j| * |τ l| * δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hd j hj l hl) (by positivity)
  have h2 : ∑ j ∈ s, ∑ l ∈ s, |τ j| * |τ l| * δ = δ * (∑ j ∈ s, |τ j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h3 : (∑ j ∈ s, |τ j|) ^ 2 ≤ s.card * ∑ j ∈ s, τ j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => |τ j|)
    simpa only [sq_abs] using h
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * |∑ j ∈ s, ∑ l ∈ s, τ j * τ l * d j l|
      ≤ 1 / 2 * (δ * (∑ j ∈ s, |τ j|) ^ 2) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 1 / 2 * (δ * (s.card * ∑ j ∈ s, τ j ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hδ) (by norm_num)
    _ = δ / 2 * (s.card * ∑ j ∈ s, τ j ^ 2) := by ring

/-- **The limit is uniform in the coefficients.** For every `η > 0`, at all large scales the
form on every combination of the nested flat divisors is within `η Σ τ_j²` of Weil's form of
the step packet. -/
theorem eventually_abs_combForm_nested_sub_le (hx₀ : 1 ≤ x₀)
    (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (hQ : X ≤ Q * x₀) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ τ : ι → ℝ,
      |combW (Ioc (x₀ * N) (X * N))
          (fun n => ∑ j ∈ s, τ j * windowDivisor (x₀ * N) (x j * N) n) / N -
        packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u)| ≤
        η * ∑ j ∈ s, τ j ^ 2 := by
  set δ : ℝ := 2 * η / (s.card + 1) with hδdef
  have hc : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ N : ℕ in atTop, ∀ j ∈ s, ∀ l ∈ s,
      |nestedEntry x₀ x N j l - stepEntry Q x₀ x j l| ≤ δ := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Filter.eventually_all_finset]
    intro l hl
    have h := (tendsto_nestedEntry hx₀ hx hQ hj hl).sub_const (stepEntry Q x₀ x j l)
    rw [sub_self] at h
    have h' := h.abs
    rw [abs_zero] at h'
    exact h'.eventually (Iic_mem_nhds hδ)
  filter_upwards [hev] with N hN τ
  rw [combForm_nested_eq hx τ N, packetForm_nested_eq hx₀ hx τ, ← mul_sub,
    ← Finset.sum_sub_distrib]
  have e : ∑ j ∈ s, (∑ l ∈ s, τ j * τ l * nestedEntry x₀ x N j l -
        ∑ l ∈ s, τ j * τ l * stepEntry Q x₀ x j l) =
      ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * (nestedEntry x₀ x N j l - stepEntry Q x₀ x j l) :=
    Finset.sum_congr rfl fun j _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  refine (abs_half_sum_sum_le τ _ hN).trans ?_
  have hsq : 0 ≤ ∑ j ∈ s, τ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfrac : δ / 2 * (s.card : ℝ) ≤ η := by
    rw [hδdef]
    have : 2 * η / ((s.card : ℝ) + 1) / 2 * (s.card : ℝ) = η * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by
      field_simp
    rw [this]
    have hle : (s.card : ℝ) / ((s.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hc]
      linarith
    nlinarith [hη.le]
  calc δ / 2 * (s.card * ∑ j ∈ s, τ j ^ 2) = δ / 2 * s.card * ∑ j ∈ s, τ j ^ 2 := by ring
    _ ≤ η * ∑ j ∈ s, τ j ^ 2 := mul_le_mul_of_nonneg_right hfrac hsq

end Nested

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
