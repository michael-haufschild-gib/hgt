import GaloisForLFunctions.HTGeometry.CentralIndexGrowthWall
import GaloisForLFunctions.HTGeometry.EulerBlowup
import GaloisForLFunctions.HTGeometry.BadIntervalCount
import GaloisForLFunctions.HTGeometry.StepwiseTelescope
import GaloisForLFunctions.HTGeometry.GoodRadiusSelection

/-!
# The growth wall at a single horizon

`DensityGrowthWall` asks for the density bound at *every* horizon `S`.  Its proof uses only one, so
the horizon can be taken as a parameter: given any `T` past the critical length, a single measure
bound at `T` suffices.

That is what a dichotomy on the *upper* density needs.  "The exceptional set has density below `1/2`
for all `S`" is a supremum condition and its negation is worthless; "there exists a horizon at which
the density is below `1/2`" is a liminf condition, and its negation — the density is eventually above
`1/2` — is exactly what the thin branch consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

variable {a : ℕ → ℂ}

set_option maxHeartbeats 2000000 in
/-- **The growth wall with a finite-measure exceptional set.**  If `ν(eᵗ) ≥ c·e^{σ φ(t)}` for every
`t ≥ t₀` outside a set of measure at most `M`, no entire function can exist: partitioning `[t₀, T]`
into steps of length `h`, at most `M/h` steps are wholly exceptional, each remaining step drops
`e^{−σφ}` by `σch/2`, and the telescoped drop bounds `T − t₀` — contradicting the freedom to take `T`
arbitrarily large. -/
theorem false_of_centralIndex_ge_exp_off_density_at {n₀ : ℕ} (ha : EntireCoeffs a) (hn₀ : a n₀ ≠ 0)
    {c σ t₀ M δ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    {T : ℝ}
    (hTge : t₀ + (2 * M + 4 * Real.exp (-(σ * logMaxTerm a t₀)) / (σ * c)) / (1 - 2 * δ) + 1 ≤ T)
    {B : Set ℝ} (hB : volume (B ∩ Set.Icc t₀ T) ≤ ENNReal.ofReal (δ * (T - t₀) + M))
    (hbd : ∀ t : ℝ, t₀ ≤ t → t ∉ B →
      c * Real.exp (σ * logMaxTerm a t) ≤ (centralIndex a (Real.exp t) : ℝ)) :
    False := by
  classical
  set φ : ℝ → ℝ := logMaxTerm a with hφ
  have hmono : ∀ {p q : ℝ}, p ≤ q → φ p ≤ φ q := fun {p q} h => logMaxTerm_mono ha hn₀ h
  set ψ₀ : ℝ := Real.exp (-(σ * φ t₀)) with hψ₀
  have hψ₀0 : 0 < ψ₀ := Real.exp_pos _
  -- choose the horizon and the step
  have hδpos : (0 : ℝ) < 1 - 2 * δ := by linarith
  have hTge' : t₀ + (2 * M + 4 * ψ₀ / (σ * c)) / (1 - 2 * δ) + 1 ≤ T := by
    rw [hψ₀]
    exact hTge
  have hTt₀ : t₀ < T := by
    have h1 : (0 : ℝ) < 4 * ψ₀ / (σ * c) := by positivity
    have h2 : (0 : ℝ) ≤ (2 * M + 4 * ψ₀ / (σ * c)) / (1 - 2 * δ) := by positivity
    linarith [hTge']
  set N : ℕ := ⌈(T - t₀) / (2 * (Real.exp (-(σ * φ T)) / (σ * c)))⌉₊ + 1 with hN
  have hN0 : 0 < N := by rw [hN]; omega
  set h : ℝ := (T - t₀) / (2 * N) with hh
  have hh0 : 0 < h := by
    rw [hh]
    have : (0 : ℝ) < 2 * N := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
      linarith
    positivity
  have h2Nh : 2 * (N : ℝ) * h = T - t₀ := by
    rw [hh]
    field_simp
  -- the step is short enough that `σ c h` stays below `e^{−σφ(T)}`
  have hhsmall : σ * c * h < Real.exp (-(σ * φ T)) := by
    have hkey : (T - t₀) / (2 * (Real.exp (-(σ * φ T)) / (σ * c))) < N := by
      rw [hN]
      have := Nat.le_ceil ((T - t₀) / (2 * (Real.exp (-(σ * φ T)) / (σ * c))))
      push_cast
      linarith
    have hden : (0 : ℝ) < 2 * (Real.exp (-(σ * φ T)) / (σ * c)) := by positivity
    rw [div_lt_iff₀ hden] at hkey
    rw [hh]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (N:ℝ))]
    have hsc : (0 : ℝ) < σ * c := by positivity
    have hexp : σ * c * ((N : ℝ) * (2 * (Real.exp (-(σ * φ T)) / (σ * c))))
        = Real.exp (-(σ * φ T)) * (2 * (N : ℝ)) := by
      field_simp
    nlinarith [mul_lt_mul_of_pos_left hkey hsc, hexp]
  -- the partition and the marked indices
  set A : ℕ → ℝ := fun i => t₀ + (i : ℝ) * h with hA
  set Φ : ℕ → ℝ := fun i => φ (A (2 * i)) with hΦ
  set Ψ : ℕ → ℝ := fun i => Real.exp (-(σ * Φ i)) with hΨ
  set G : Finset ℕ := (Finset.range N).filter
    (fun i => ∃ s ∈ Set.Ico (A (2 * i)) (A (2 * i + 1)), s ∉ B) with hG
  have hAmono : ∀ i j : ℕ, i ≤ j → A i ≤ A j := by
    intro i j hij
    rw [hA]
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith [hh0]
  have hAt₀ : ∀ i : ℕ, t₀ ≤ A i := by
    intro i
    rw [hA]
    have : (0 : ℝ) ≤ (i : ℝ) * h := by positivity
    linarith
  have hAT : ∀ i : ℕ, i ≤ N → A (2 * i) ≤ T := by
    intro i hi
    rw [hA]
    have hle : ((2 * i : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast
      have : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      linarith
    nlinarith [hle, hh0, h2Nh]
  -- the value stays above the step
  have hΨbig : ∀ i : ℕ, i ≤ N → σ * (c * h) ≤ Ψ i := by
    intro i hi
    have hle : φ (A (2 * i)) ≤ φ T := hmono (hAT i hi)
    have : Real.exp (-(σ * φ T)) ≤ Real.exp (-(σ * Φ i)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hΦ]
      nlinarith [hle, hσ]
    have hrw : σ * (c * h) = σ * c * h := by ring
    rw [hΨ, hrw]
    linarith [hhsmall, this]
  -- monotonicity of `Φ`, hence `Ψ` never increases
  have hΦmono : ∀ i : ℕ, Φ i ≤ Φ (i + 1) := by
    intro i
    rw [hΦ]
    refine hmono (hAmono _ _ ?_)
    omega
  have hbad : ∀ i : ℕ, i ∉ G → Ψ (i + 1) ≤ Ψ i := by
    intro i _
    rw [hΨ]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hΦmono i, hσ]
  -- a marked index drops the value
  have hgood : ∀ i ∈ G, Ψ (i + 1) ≤ Ψ i - σ * (c * h) / 2 := by
    intro i hi
    rw [hG, Finset.mem_filter] at hi
    obtain ⟨hiN, s, hs, hsB⟩ := hi
    have hiN' : i < N := Finset.mem_range.mp hiN
    have hst₀ : t₀ ≤ s := le_trans (hAt₀ _) hs.1
    have hnu := hbd s hst₀ hsB
    have hsle : s ≤ A (2 * (i + 1)) := by
      refine le_trans hs.2.le (hAmono _ _ ?_)
      omega
    have hgrow := centralIndex_mul_le_logMaxTerm_sub ha hn₀ hsle
    have hgap : h ≤ A (2 * (i + 1)) - s := by
      have hA1 : A (2 * i + 1) + h = A (2 * (i + 1)) := by
        rw [hA]
        push_cast
        ring
      linarith [hs.2, hA1]
    have hφs : Φ i ≤ φ s := hmono hs.1
    have hnu0 : (0 : ℝ) ≤ (centralIndex a (Real.exp s) : ℝ) := Nat.cast_nonneg _
    have hstep : Φ i + (c * h) * Real.exp (σ * Φ i) ≤ Φ (i + 1) := by
      have hexp : Real.exp (σ * Φ i) ≤ Real.exp (σ * φ s) :=
        Real.exp_le_exp.mpr (by nlinarith [hφs, hσ])
      have hcc : c * Real.exp (σ * Φ i) ≤ (centralIndex a (Real.exp s) : ℝ) := by
        nlinarith [hnu, hexp, hc]
      have h1 : c * h * Real.exp (σ * Φ i) ≤ (centralIndex a (Real.exp s) : ℝ) * h := by
        nlinarith [hcc, hh0]
      have h2 : (centralIndex a (Real.exp s) : ℝ) * h
          ≤ (centralIndex a (Real.exp s) : ℝ) * (A (2 * (i + 1)) - s) :=
        mul_le_mul_of_nonneg_left hgap hnu0
      have h3 : φ (A (2 * (i + 1))) - φ s
          ≥ (centralIndex a (Real.exp s) : ℝ) * (A (2 * (i + 1)) - s) := hgrow
      rw [hΦ]
      show φ (A (2 * i)) + c * h * Real.exp (σ * φ (A (2 * i))) ≤ φ (A (2 * (i + 1)))
      rw [hΦ] at hφs
      linarith [h1, h2, h3, hφs]
    exact euler_step (by positivity) hσ hstep (hΨbig i (le_of_lt hiN'))
  -- telescope
  have htel := le_sub_card_mul_of_stepwise hgood hbad N
  have hfilter : G.filter (fun i => i < N) = G := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    rw [hG, Finset.mem_filter] at hi
    exact Finset.mem_range.mp hi.1
  rw [hfilter] at htel
  -- count the wholly bad intervals
  set S : Finset ℕ := (Finset.range N) \ G with hS
  have hSsub : ∀ j ∈ S.image (fun i : ℕ => 2 * i),
      Set.Ico (t₀ + (j : ℝ) * h) (t₀ + ((j : ℝ) + 1) * h) ⊆ B ∩ Set.Icc t₀ T := by
    intro j hj
    obtain ⟨i, hiS, hij⟩ := Finset.mem_image.mp hj
    rw [← hij]
    rw [hS, Finset.mem_sdiff] at hiS
    intro x hx
    have hxI : x ∈ Set.Icc t₀ T := by
      obtain ⟨hx1, hx2⟩ := hx
      have hiN : i < N := Finset.mem_range.mp hiS.1
      constructor
      · have hnn : (0 : ℝ) ≤ ((2 * i : ℕ) : ℝ) * h := by positivity
        linarith [hx1, hnn]
      · have hib : ((2 * i : ℕ) : ℝ) + 1 ≤ 2 * (N : ℝ) := by
          push_cast
          have : (i : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hiN
          linarith
        have hmul : (((2 * i : ℕ) : ℝ) + 1) * h ≤ 2 * (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right hib hh0.le
        push_cast at hx2 hmul ⊢
        linarith [h2Nh]
    refine ⟨?_, hxI⟩
    by_contra hxB
    refine absurd ?_ hiS.2
    rw [hG, Finset.mem_filter]
    refine ⟨hiS.1, x, ?_, hxB⟩
    rw [hA]
    push_cast at hx ⊢
    exact hx
  have hMT : (0 : ℝ) ≤ δ * (T - t₀) + M := by
    have : (0 : ℝ) ≤ δ * (T - t₀) := by
      have : (0 : ℝ) ≤ T - t₀ := by linarith
      positivity
    linarith
  have hcard := card_mul_le_of_subset_of_volume_le hh0 hMT hB hSsub
  have hcardeq : (S.image (fun i : ℕ => 2 * i)).card = S.card :=
    Finset.card_image_of_injective _ (fun p q hpq => by omega)
  rw [hcardeq] at hcard
  have hGcard : (N : ℝ) - (S.card : ℝ) = (G.card : ℝ) := by
    have hGsub : G ⊆ Finset.range N := by
      intro i hi
      rw [hG, Finset.mem_filter] at hi
      exact hi.1
    have hinter : G ∩ Finset.range N = G := Finset.inter_eq_left.mpr hGsub
    have : S.card = N - G.card := by
      rw [hS, Finset.card_sdiff, hinter, Finset.card_range]
    rw [this]
    have hle : G.card ≤ N := le_trans (Finset.card_le_card hGsub) (by simp)
    push_cast [Nat.cast_sub hle]
    ring
  -- assemble the contradiction
  have hΨN : 0 < Ψ N := Real.exp_pos _
  have hΨ0 : Ψ 0 = ψ₀ := by
    rw [hΨ, hΦ, hψ₀, hA]
    norm_num
  rw [hΨ0] at htel
  have hGbound : (G.card : ℝ) * (σ * (c * h) / 2) < ψ₀ := by linarith [htel, hΨN]
  have hScard : (S.card : ℝ) * h ≤ δ * (T - t₀) + M := hcard
  have hkey : ((N : ℝ) - (S.card : ℝ)) * (σ * c * h) / 2 < ψ₀ := by
    rw [hGcard]
    have : (G.card : ℝ) * (σ * (c * h) / 2) = (G.card : ℝ) * (σ * c * h) / 2 := by ring
    linarith [hGbound, this]
  have hsc : (0 : ℝ) < σ * c := by positivity
  have hfinal : (1 - 2 * δ) * ((T - t₀) / 2) - M < 2 * ψ₀ / (σ * c) := by
    have hexpand : ((N : ℝ) - (S.card : ℝ)) * (σ * c * h) / 2
        = (σ * c / 2) * ((N : ℝ) * h - (S.card : ℝ) * h) := by ring
    rw [hexpand] at hkey
    have hNh : (N : ℝ) * h = (T - t₀) / 2 := by linarith [h2Nh]
    rw [hNh] at hkey
    have hSb : (S.card : ℝ) * h ≤ δ * (T - t₀) + M := hScard
    rw [lt_div_iff₀ hsc]
    nlinarith [hkey, hSb, hsc]
  have hbase : (1 - 2 * δ) * ((t₀ + (2 * M + 4 * ψ₀ / (σ * c)) / (1 - 2 * δ) + 1 - t₀) / 2)
      = (2 * M + 4 * ψ₀ / (σ * c)) / 2 + (1 - 2 * δ) / 2 := by
    field_simp
    ring
  have hmonoT : (1 - 2 * δ) * ((t₀ + (2 * M + 4 * ψ₀ / (σ * c)) / (1 - 2 * δ) + 1 - t₀) / 2)
      ≤ (1 - 2 * δ) * ((T - t₀) / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hδpos)
    linarith [hTge']
  have hδ1 : (0 : ℝ) < (1 - 2 * δ) / 2 := by linarith
  have hQ : 4 * ψ₀ / (σ * c) = 2 * (2 * ψ₀ / (σ * c)) := by ring
  rw [hQ] at hbase hmonoT
  linarith [hfinal, hmonoT, hbase, hδ1]

end GaloisForLFunctions.HTGeometry
