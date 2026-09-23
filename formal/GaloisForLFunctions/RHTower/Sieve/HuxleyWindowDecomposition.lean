import GaloisForLFunctions.RHTower.Sieve.HuxleyFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.MaynardColorFiberCounting

/-!
# Huxley large values by short ordinate windows

The local Huxley estimate needs its second-derivative Gram envelope to be absorbed by the
large-value threshold.  Below the global square scale this is recovered by partitioning a bounded
ordinate set into intervals of length `W`, applying the local estimate on every interval, and
summing.  The number of intervals is at most `floor (T / W) + 1`.

Choosing `W` at the largest locally absorbing scale is the source of Huxley's classical cubic
term: local cost `G N / V^(2 : ℕ)` times `T / W`, with `W` proportional to `V^(4 : ℕ) / G^(2 : ℕ)`, is
`T N G^(3 : ℕ) / V^(6 : ℕ)`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Number of half-open windows of length `W` needed to cover `[0,T]`. -/
def huxleyWindowCount (T W : ℝ) : ℕ := ⌊T / W⌋₊ + 1

theorem huxleyWindowCount_pos (T W : ℝ) : 0 < huxleyWindowCount T W := by
  simp only [huxleyWindowCount]
  omega

theorem huxleyWindowCount_cast_le {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W) :
    (huxleyWindowCount T W : ℝ) ≤ T / W + 1 := by
  have hquot : 0 ≤ T / W := div_nonneg hT hW.le
  have hfloor : ((⌊T / W⌋₊ : ℕ) : ℝ) ≤ T / W := Nat.floor_le hquot
  simp only [huxleyWindowCount, Nat.cast_add, Nat.cast_one]
  linarith

/-- Canonical window color.  Values outside `[0,T]` are sent to color zero; all applications
provide the range hypothesis on the finite set being colored. -/
def huxleyWindowColor (T W : ℝ) (lam : ℕ → ℝ) (r : ℕ) :
    Fin (huxleyWindowCount T W) :=
  if h : 0 ≤ lam r ∧ lam r ≤ T then
    ⟨⌊lam r / W⌋₊, by
      by_cases hWpos : 0 < W
      · have hdiv : lam r / W ≤ T / W :=
          (div_le_div_iff_of_pos_right hWpos).2 h.2
        exact lt_of_le_of_lt (Nat.floor_le_floor hdiv) (Nat.lt_succ_self _)
      · have hzero : ⌊lam r / W⌋₊ = 0 := by
          apply Nat.floor_eq_zero.mpr
          exact (div_nonpos_of_nonneg_of_nonpos h.1
            (le_of_not_gt hWpos)).trans_lt (by norm_num)
        rw [hzero]
        exact huxleyWindowCount_pos T W⟩
  else
    ⟨0, huxleyWindowCount_pos T W⟩

/-- Two nonnegative ordinates in the same canonical window differ by less than its length. -/
theorem abs_sub_lt_of_huxleyWindowColor_eq
    {T W : ℝ} {lam : ℕ → ℝ} {r s : ℕ}
    (hW : 0 < W) (hr0 : 0 ≤ lam r) (hrT : lam r ≤ T)
    (hs0 : 0 ≤ lam s) (hsT : lam s ≤ T)
    (hcolor : huxleyWindowColor T W lam r = huxleyWindowColor T W lam s) :
    |lam s - lam r| < W := by
  have hfloor : ⌊lam r / W⌋₊ = ⌊lam s / W⌋₊ := by
    have hval := congrArg (fun q : Fin (huxleyWindowCount T W) => (q : ℕ)) hcolor
    simpa only [huxleyWindowColor, hr0, hrT, hs0, hsT, and_self,
      dite_true] using hval
  have hqr0 : 0 ≤ lam r / W := div_nonneg hr0 hW.le
  have hqs0 : 0 ≤ lam s / W := div_nonneg hs0 hW.le
  have hrLower : ((⌊lam r / W⌋₊ : ℕ) : ℝ) ≤ lam r / W := Nat.floor_le hqr0
  have hsLower : ((⌊lam s / W⌋₊ : ℕ) : ℝ) ≤ lam s / W := Nat.floor_le hqs0
  have hrUpper : lam r / W < ((⌊lam r / W⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hsUpper : lam s / W < ((⌊lam s / W⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloorCast : ((⌊lam r / W⌋₊ : ℕ) : ℝ) =
      ((⌊lam s / W⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor
  rw [← hfloorCast] at hsLower hsUpper
  have hrLower' : ((⌊lam r / W⌋₊ : ℕ) : ℝ) * W ≤ lam r :=
    (le_div_iff₀ hW).mp hrLower
  have hsLower' : ((⌊lam r / W⌋₊ : ℕ) : ℝ) * W ≤ lam s :=
    (le_div_iff₀ hW).mp hsLower
  have hrUpper' : lam r < (((⌊lam r / W⌋₊ : ℕ) : ℝ) + 1) * W :=
    (div_lt_iff₀ hW).mp hrUpper
  have hsUpper' : lam s < (((⌊lam r / W⌋₊ : ℕ) : ℝ) + 1) * W :=
    (div_lt_iff₀ hW).mp hsUpper
  rw [abs_lt]
  constructor <;> linarith

/-- **Window-summed multi-block Huxley theorem.**  Local absorption is required only at window
length `W`; no absorption at the ambient height `T` is assumed. -/
theorem huxley_multiblock_large_values_finset_windowed
    {ι : Type*} [Fintype ι] {K : ℕ}
    (N : ι → ℕ) (hN : ∀ q, 1 ≤ N q)
    (a : ∀ q, EuclideanSpace ℂ (Fin (N q)))
    (G U B : ι → ℝ) {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T W V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hW : 0 < W) (hV : 0 < V)
    (hmass : ∀ q, ‖a q‖ ^ (2 : ℕ) ≤ G q)
    (hU : ∀ q, 0 < U q)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ T)
    (hnear : ∀ q, 3 * U q ≤ 4 * Real.pi * (N q : ℝ))
    (hlamW : ∀ q, logDyadicLambda (N q) W ≤ 1)
    (hB : ∀ q, logDyadicSecondEnvelope (N q) (U q) W ≤ B q)
    (hB1 : ∀ q, 1 ≤ B q)
    (hbig : ∀ r ∈ S,
      V ≤ ∑ q : ι, ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖)
    (habsorb : (Fintype.card ι : ℝ) * ∑ q : ι, G q * B q ≤ V ^ (2 : ℕ) / 2) :
    (S.card : ℝ) * V ^ (2 : ℕ) ≤
      (huxleyWindowCount T W : ℝ) *
        (2 * (Fintype.card ι : ℝ) * ∑ q : ι,
          G q * ((N q : ℝ) + (12 * Real.pi * (N q : ℝ) / delta) *
            ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  let color : ℕ → Fin (huxleyWindowCount T W) := huxleyWindowColor T W lam
  let H : ℝ := 2 * (Fintype.card ι : ℝ) * ∑ q : ι,
    G q * ((N q : ℝ) + (12 * Real.pi * (N q : ℝ) / delta) *
      ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
  have hfibre : ∀ c : Fin (huxleyWindowCount T W),
      ((((S.filter fun r => color r = c).card : ℕ) : ℝ) * V ^ (2 : ℕ)) ≤ H := by
    intro c
    let Sf : Finset ℕ := S.filter fun r => color r = c
    have hSfS : Sf ⊆ S := Finset.filter_subset _ _
    have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
    have hSfDiam : ∀ r ∈ Sf, ∀ s ∈ Sf, |lam s - lam r| ≤ W := by
      intro r hr s hs
      have hrS := hSfS hr
      have hsS := hSfS hs
      have hrcolor : color r = c := (Finset.mem_filter.mp hr).2
      have hscolor : color s = c := (Finset.mem_filter.mp hs).2
      exact (abs_sub_lt_of_huxleyWindowColor_eq hW
        (hband r hrS).1 (hband r hrS).2 (hband s hsS).1 (hband s hsS).2
        (by simpa only [color] using hrcolor.trans hscolor.symm)).le
    have hlocal := huxley_multiblock_large_values_finset N hN a G U B
      hSfRange hdelta hV hmass hU hgap hnear hlamW hB hB1 hSfDiam
      (fun r hr => hbig r (hSfS hr)) habsorb
    simpa only [Sf, H] using hlocal
  have hsum := card_mul_sq_le_card_labels_mul_of_color_fibre_bounds
    S color hV (fun _ => V) (fun _ => H) (fun _ => le_rfl) (fun _ => le_rfl)
      (fun c => hfibre c)
  simpa only [color, H, Fintype.card_fin] using hsum

end RHTower.Sieve
