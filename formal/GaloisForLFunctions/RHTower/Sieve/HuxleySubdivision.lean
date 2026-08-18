import GaloisForLFunctions.RHTower.Sieve.HuxleyLargeValues

/-!
# Huxley's window subdivision and the global large-values count

`Sieve/HuxleyLargeValues` proves the *local* Huxley estimate: on a frequency window whose diameter
`W` is small enough that the second-derivative envelope is absorbed by the threshold, the number of
`delta`-separated large values is at most `2 G (N + 12 pi N (1 + log K)/delta)/V^2`.

Huxley's global theorem is obtained by cutting the whole frequency range into windows of length `W`
and adding the local counts.  The combinatorial half of that step is isolated here as
`card_le_of_window_bound`, which needs nothing about Dirichlet polynomials: a strictly increasing
family confined to a range of length `Ttot`, all of whose runs of consecutive indices spanning at
most `W` are shorter than `C`, has at most `(floor (Ttot/W) + 1) * C` members.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Window subdivision.**  A monotone family confined to a range of length `Ttot`, every one of
whose consecutive index runs of frequency spread at most `W` has at most `C` members, has at most
`(floor (Ttot/W) + 1) * C` members in total. -/
theorem card_le_of_window_bound {lam : ℕ → ℝ} (hmono : Monotone lam)
    {W Ttot C : ℝ} (hW : 0 < W) (R : ℕ)
    (hspread : ∀ r, r ≤ R → lam r - lam 0 ≤ Ttot)
    (hlocal : ∀ j m : ℕ, j + m ≤ R → lam (j + m) - lam j ≤ W → ((m : ℝ) + 1) ≤ C) :
    ((R : ℝ) + 1) ≤ ((⌊Ttot / W⌋₊ : ℝ) + 1) * C := by
  have hC1 : (1 : ℝ) ≤ C := by
    have h := hlocal 0 0 (Nat.zero_le _) (by simpa using hW.le)
    simpa using h
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hnn : ∀ r : ℕ, (0 : ℝ) ≤ (lam r - lam 0) / W := by
    intro r
    have h0 : lam 0 ≤ lam r := hmono (Nat.zero_le r)
    exact div_nonneg (by linarith) hW.le
  have hbmem : ∀ r ∈ Finset.range (R + 1),
      (⌊(lam r - lam 0) / W⌋₊) ∈ Finset.range (⌊Ttot / W⌋₊ + 1) := by
    intro r hr
    have hrR : r ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hle : (lam r - lam 0) / W ≤ Ttot / W :=
      div_le_div_of_nonneg_right (hspread r hrR) hW.le
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_mono hle))
  have hcard := Finset.card_eq_sum_card_fiberwise hbmem
  have hfiber : ∀ c ∈ Finset.range (⌊Ttot / W⌋₊ + 1),
      (((Finset.range (R + 1)).filter
        (fun r => ⌊(lam r - lam 0) / W⌋₊ = c)).card : ℝ) ≤ C := by
    intro c _
    set S := (Finset.range (R + 1)).filter
      (fun r => ⌊(lam r - lam 0) / W⌋₊ = c) with hS
    rcases S.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]
      simpa using hC0
    · have hjS : S.min' hne ∈ S := S.min'_mem hne
      have hMS : S.max' hne ∈ S := S.max'_mem hne
      set j := S.min' hne with hj
      set M := S.max' hne with hM
      have hjM : j ≤ M := S.min'_le M hMS
      have hMR : M ≤ R :=
        Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hMS).1)
      have hjc : ⌊(lam j - lam 0) / W⌋₊ = c := (Finset.mem_filter.1 hjS).2
      have hMc : ⌊(lam M - lam 0) / W⌋₊ = c := (Finset.mem_filter.1 hMS).2
      have hdiff : (lam M - lam 0) / W - (lam j - lam 0) / W = (lam M - lam j) / W := by
        rw [div_sub_div_same]
        congr 1
        ring
      have h1 : ((c : ℝ)) ≤ (lam j - lam 0) / W := by
        rw [← hjc]
        exact Nat.floor_le (hnn j)
      have h2 : (lam M - lam 0) / W < (c : ℝ) + 1 := by
        rw [← hMc]
        exact Nat.lt_floor_add_one _
      have h4 : (lam M - lam j) / W < 1 := by
        rw [← hdiff]
        linarith
      have hwin : lam M - lam j ≤ W := le_of_lt ((div_lt_one hW).1 h4)
      have hsub : S ⊆ Finset.Icc j M := by
        intro x hx
        exact Finset.mem_Icc.2 ⟨S.min'_le x hx, Finset.le_max' S x hx⟩
      have hcs : S.card ≤ M + 1 - j := by
        have h := Finset.card_le_card hsub
        simpa [Nat.card_Icc] using h
      have hloc := hlocal j (M - j) (by omega) (by
        have he : j + (M - j) = M := by omega
        rw [he]
        exact hwin)
      have hcast : ((M + 1 - j : ℕ) : ℝ) = ((M - j : ℕ) : ℝ) + 1 := by
        have he : M + 1 - j = (M - j) + 1 := by omega
        rw [he]
        push_cast
        ring
      calc ((S.card : ℕ) : ℝ) ≤ ((M + 1 - j : ℕ) : ℝ) := by exact_mod_cast hcs
        _ = ((M - j : ℕ) : ℝ) + 1 := hcast
        _ ≤ C := hloc
  have hstep : (((Finset.range (R + 1)).card : ℕ) : ℝ)
      = ∑ c ∈ Finset.range (⌊Ttot / W⌋₊ + 1),
          ((((Finset.range (R + 1)).filter
            (fun r => ⌊(lam r - lam 0) / W⌋₊ = c)).card : ℕ) : ℝ) := by
    rw [hcard]
    push_cast
    ring
  have hlhs : (((Finset.range (R + 1)).card : ℕ) : ℝ) = (R : ℝ) + 1 := by
    rw [Finset.card_range]
    push_cast
    ring
  have hsum : ∑ _c ∈ Finset.range (⌊Ttot / W⌋₊ + 1), C
      = ((⌊Ttot / W⌋₊ : ℝ) + 1) * C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hle := Finset.sum_le_sum hfiber
  rw [← hstep, hlhs, hsum] at hle
  exact hle

/-- **Huxley's global large-values theorem.**  Subdividing the frequency range into windows of
diameter `W` — short enough that the second-derivative envelope `B` is absorbed by `V^2/2` — and
adding the local counts gives the global count with the subdivision factor `floor (Ttot/W) + 1`. -/
theorem huxley_global_large_values {N : ℕ} (hN : 1 ≤ N)
    (a : EuclideanSpace ℂ (Fin N)) {lam : ℕ → ℝ}
    {delta U W Ttot V G B : ℝ} (hdelta : 0 < delta) (hU : 0 < U) (hV : 0 < V) (hW : 0 < W)
    (hmass : ‖a‖ ^ 2 ≤ G)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamW : logDyadicLambda N W ≤ 1)
    (hB : logDyadicSecondEnvelope N U W ≤ B) (hB1 : 1 ≤ B)
    (R : ℕ)
    (hspread : ∀ r, r ≤ R → lam r - lam 0 ≤ Ttot)
    (hbig : ∀ r, r ≤ R → V ≤ ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖)
    (habsorb : G * B ≤ V ^ 2 / 2) :
    ((R : ℝ) + 1) * V ^ 2
      ≤ ((⌊Ttot / W⌋₊ : ℝ) + 1) *
        (2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1))) := by
  have hmono : Monotone lam := by
    have hs : StrictMono lam := strictMono_nat_of_lt_succ (fun n => by
      have h := hgap n
      linarith)
    exact hs.monotone
  have hG0 : (0 : ℝ) ≤ G := le_trans (by positivity) hmass
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  set Cnum : ℝ := 2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
      * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1)) with hCnum
  have hkey : ((R : ℝ) + 1) ≤ ((⌊Ttot / W⌋₊ : ℝ) + 1) * (Cnum / V ^ 2) := by
    refine card_le_of_window_bound hmono hW R hspread ?_
    intro j m hjm hwin
    have hgap' : ∀ i, lam (j + i) + delta ≤ lam (j + (i + 1)) := by
      intro i
      have h := hgap (j + i)
      have he : j + (i + 1) = (j + i) + 1 := by omega
      rw [he]
      exact h
    have hdiam' : ∀ r ∈ Finset.range (m + 1), ∀ s ∈ Finset.range (m + 1),
        |lam (j + s) - lam (j + r)| ≤ W := by
      intro r hr s hs
      have hr' : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      have hs' : s ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
      have h1 : lam j ≤ lam (j + r) := hmono (by omega)
      have h2 : lam (j + r) ≤ lam (j + m) := hmono (by omega)
      have h3 : lam j ≤ lam (j + s) := hmono (by omega)
      have h4 : lam (j + s) ≤ lam (j + m) := hmono (by omega)
      rw [abs_le]
      constructor <;> linarith
    have hbig' : ∀ r ∈ Finset.range (m + 1),
        V ≤ ‖⟪dyadicDirRow N (lam (j + r)), a⟫_ℂ‖ := by
      intro r hr
      have hr' : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      exact hbig (j + r) (by omega)
    have hloc := huxley_local_large_values (lam := fun i => lam (j + i)) hN a hdelta hU hV
      hmass hgap' hnear hlamW hB hB1 m hdiam' hbig' habsorb
    have hharm : ∑ i ∈ Finset.range (m + 1), 1 / ((i : ℝ) + 1)
        ≤ ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1) := by
      have hmR : m + 1 ≤ R + 1 := Nat.succ_le_succ (le_trans (Nat.le_add_left m j) hjm)
      have hsub' : Finset.range (m + 1) ⊆ Finset.range (R + 1) := by
        intro x hx
        exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hmR)
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub' ?_
      intro i _ _
      positivity
    have hup : 2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
        * ∑ i ∈ Finset.range (m + 1), 1 / ((i : ℝ) + 1)) ≤ Cnum := by
      rw [hCnum]
      have hcoef : (0 : ℝ) ≤ 12 * Real.pi * (N : ℝ) / delta := by positivity
      have hinner := mul_le_mul_of_nonneg_left hharm hcoef
      nlinarith [hG0, hinner]
    have hfin : ((m : ℝ) + 1) * V ^ 2 ≤ Cnum := le_trans hloc hup
    rw [le_div_iff₀ hV2]
    exact hfin
  calc ((R : ℝ) + 1) * V ^ 2
      ≤ ((⌊Ttot / W⌋₊ : ℝ) + 1) * (Cnum / V ^ 2) * V ^ 2 := by
        exact mul_le_mul_of_nonneg_right hkey hV2.le
    _ = ((⌊Ttot / W⌋₊ : ℝ) + 1) * Cnum := by
        field_simp

end RHTower.Sieve
