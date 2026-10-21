import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwoTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiRealSmoothBump
import GaloisForLFunctions.RHTower.L2FourierConjugation

/-!
# Permutation symmetry of `|I_m|` (proof of Guth–Maynard Proposition 7.2, first step)

Relabelling `(t₁, t₂, t₃) ↦ (t₂, t₃, t₁)` in `I_m = N³ Σ ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)`
gives the cyclic invariance `I_{(m₂,m₃,m₁)} = I_{(m₁,m₂,m₃)}`; for a real bump `w`,
`conj ĥ_t(ξ) = ĥ_{−t}(−ξ)` and the relabelling `t₁ ↔ t₂` give `conj I_m = I_{(−m₁,−m₃,−m₂)}`
(the paper states this as `I_{(m₁,m₂,m₃)} = conj I_{(m₂,m₁,m₃)}`; the exact identity carries the sign
change of all three frequencies, which is irrelevant for `|I_m|`). The two maps generate all six
permutations of `(|m₁|, |m₂|, |m₃|)` and preserve every box `0 < |m_i| ≤ K`, so a box sum of `|I_m|`
is at most six times its sum over the sorted frequencies `|m₁| ≤ |m₂| ≤ |m₃|`.
-/

set_option autoImplicit false

open Set

namespace RHTower.GuthMaynard

noncomputable section

/-- Cyclic invariance `I_{(m₂,m₃,m₁)} = I_{(m₁,m₂,m₃)}`. -/
theorem cubicTerm_cycle (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) :
    cubicTerm w W N m₂ m₃ m₁ = cubicTerm w W N m₁ m₂ m₃ := by
  unfold cubicTerm
  congr 1
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

/-- For a real bump, `conj h_t = h_{−t}`. -/
theorem conj_cglSmoothBumpHt (w : CGLRealSmoothBump) (t x : ℝ) :
    (starRingEnd ℂ) (cglSmoothBumpHt w.toCGLSmoothBump t x) =
      cglSmoothBumpHt w.toCGLSmoothBump (-t) x := by
  rw [cglSmoothBumpHt_eq, cglSmoothBumpHt_eq, map_mul, map_pow,
    Complex.conj_eq_iff_im.mpr (w.imaginary_zero x)]
  congr 1
  unfold lagPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

/-- For a real bump, `conj ĥ_t(ξ) = ĥ_{−t}(−ξ)`. -/
theorem conj_bumpFourier (w : CGLRealSmoothBump) (t ξ : ℝ) :
    (starRingEnd ℂ) (bumpFourier w.toCGLSmoothBump t ξ) =
      bumpFourier w.toCGLSmoothBump (-t) (-ξ) := by
  have h : (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) =
      fun x => (starRingEnd ℂ) (cglSmoothBumpHt w.toCGLSmoothBump (-t) x) := by
    funext x; rw [conj_cglSmoothBumpHt, neg_neg]
  unfold bumpFourier
  rw [h]
  exact conj_fourierIntegral_conj _ ξ

/-- For a real bump, `conj I_m = I_{(−m₁,−m₃,−m₂)}`. -/
theorem conj_cubicTerm (w : CGLRealSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) :
    (starRingEnd ℂ) (cubicTerm w.toCGLSmoothBump W N m₁ m₂ m₃) =
      cubicTerm w.toCGLSmoothBump W N (-m₁) (-m₃) (-m₂) := by
  unfold cubicTerm
  simp only [map_mul, map_pow, Complex.conj_ofReal, map_sum, conj_bumpFourier]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [neg_sub, Int.cast_neg, neg_mul]
  ring

theorem norm_cubicTerm_flip (w : CGLRealSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) :
    ‖cubicTerm w.toCGLSmoothBump W N (-m₁) (-m₃) (-m₂)‖ =
      ‖cubicTerm w.toCGLSmoothBump W N m₁ m₂ m₃‖ := by
  rw [← conj_cubicTerm, Complex.norm_conj]

/-! ### Reduction to sorted frequencies -/

/-- `|m₁| ≤ |m₂| ≤ |m₃|`. -/
def IsSortedFrequency (m : ℤ × ℤ × ℤ) : Prop :=
  |m.1| ≤ |m.2.1| ∧ |m.2.1| ≤ |m.2.2|

instance : DecidablePred IsSortedFrequency := fun m => by
  unfold IsSortedFrequency; infer_instance

/-- Reindexing a filtered sum along a bijection that preserves the index set and the summand. -/
theorem sum_filter_comp_eq {X : Type*} [DecidableEq X] (s : Finset X) (F : X → ℝ) (g h : X → X)
    (hgh : ∀ m, g (h m) = m) (hhg : ∀ m, h (g m) = m) (hs : ∀ m, m ∈ s ↔ g m ∈ s)
    (hF : ∀ m, F (g m) = F m) (p : X → Prop) [DecidablePred p] :
    ∑ m ∈ s.filter (fun m => p (g m)), F m = ∑ m ∈ s.filter p, F m := by
  refine Finset.sum_nbij' g h (fun m hm => ?_) (fun m hm => ?_) (fun m _ => hhg m)
    (fun m _ => hgh m) (fun m _ => (hF m).symm)
  · rw [Finset.mem_filter] at hm ⊢
    exact ⟨(hs m).mp hm.1, hm.2⟩
  · rw [Finset.mem_filter] at hm ⊢
    refine ⟨(hs (h m)).mpr ?_, ?_⟩ <;> rw [hgh m]
    · exact hm.1
    · exact hm.2

/-- The cyclic shift `(m₁, m₂, m₃) ↦ (m₂, m₃, m₁)`. -/
def freqCycle (m : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (m.2.1, m.2.2, m.1)

/-- The reflection `(m₁, m₂, m₃) ↦ (−m₁, −m₃, −m₂)`. -/
def freqFlip (m : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-m.1, -m.2.2, -m.2.1)

/-- **Sorting at cost six.** If the finite set `s` and the nonnegative `F` are invariant under the
cyclic shift and the reflection, then `Σ_s F ≤ 6 Σ_{s, |m₁|≤|m₂|≤|m₃|} F`. -/
theorem sum_le_six_mul_sum_sorted (s : Finset (ℤ × ℤ × ℤ)) (F : ℤ × ℤ × ℤ → ℝ)
    (hF0 : ∀ m, 0 ≤ F m) (hsc : ∀ m, m ∈ s ↔ freqCycle m ∈ s) (hsf : ∀ m, m ∈ s ↔ freqFlip m ∈ s)
    (hFc : ∀ m, F (freqCycle m) = F m) (hFf : ∀ m, F (freqFlip m) = F m) :
    ∑ m ∈ s, F m ≤ 6 * ∑ m ∈ s.filter IsSortedFrequency, F m := by
  -- the six permutations of `(|m₁|, |m₂|, |m₃|)`, each with its inverse
  let g₁ := freqCycle
  let g₂ := fun m => freqCycle (freqCycle m)
  let g₃ := freqFlip
  let g₄ := fun m => freqFlip (freqCycle (freqCycle m))
  let g₅ := fun m => freqFlip (freqCycle m)
  have e₁ := sum_filter_comp_eq s F g₁ g₂ (fun _ => rfl) (fun _ => rfl) hsc hFc IsSortedFrequency
  have e₂ := sum_filter_comp_eq s F g₂ g₁ (fun _ => rfl) (fun _ => rfl)
    (fun m => (hsc m).trans (hsc _)) (fun m => (hFc _).trans (hFc m)) IsSortedFrequency
  have e₃ := sum_filter_comp_eq s F g₃ g₃ (fun m => by simp [g₃, freqFlip])
    (fun m => by simp [g₃, freqFlip]) hsf hFf IsSortedFrequency
  have e₄ := sum_filter_comp_eq s F g₄ g₄ (fun m => by simp [g₄, freqFlip, freqCycle])
    (fun m => by simp [g₄, freqFlip, freqCycle])
    (fun m => ((hsc m).trans (hsc _)).trans (hsf _))
    (fun m => ((hFf _).trans (hFc _)).trans (hFc m)) IsSortedFrequency
  have e₅ := sum_filter_comp_eq s F g₅ g₅ (fun m => by simp [g₅, freqFlip, freqCycle])
    (fun m => by simp [g₅, freqFlip, freqCycle]) (fun m => (hsc m).trans (hsf _))
    (fun m => (hFf _).trans (hFc m)) IsSortedFrequency
  -- every frequency is sorted by one of the six maps
  have hcover : ∀ m : ℤ × ℤ × ℤ, F m ≤
      (if IsSortedFrequency m then F m else 0) + (if IsSortedFrequency (g₁ m) then F m else 0) +
      (if IsSortedFrequency (g₂ m) then F m else 0) + (if IsSortedFrequency (g₃ m) then F m else 0) +
      (if IsSortedFrequency (g₄ m) then F m else 0) +
      (if IsSortedFrequency (g₅ m) then F m else 0) := by
    intro m
    have h := hF0 m
    obtain ⟨a, b, c⟩ := m
    simp only [g₁, g₂, g₃, g₄, g₅, freqCycle, freqFlip, IsSortedFrequency, abs_neg]
    rcases le_total |a| |b| with hab | hab <;> rcases le_total |b| |c| with hbc | hbc <;>
      rcases le_total |a| |c| with hac | hac <;>
      simp [hab, hbc, hac] <;> split_ifs <;> linarith
  calc ∑ m ∈ s, F m
      ≤ ∑ m ∈ s, ((if IsSortedFrequency m then F m else 0) +
          (if IsSortedFrequency (g₁ m) then F m else 0) +
          (if IsSortedFrequency (g₂ m) then F m else 0) +
          (if IsSortedFrequency (g₃ m) then F m else 0) +
          (if IsSortedFrequency (g₄ m) then F m else 0) +
          (if IsSortedFrequency (g₅ m) then F m else 0)) := Finset.sum_le_sum fun m _ => hcover m
    _ = ∑ m ∈ s.filter IsSortedFrequency, F m + ∑ m ∈ s.filter (fun m => IsSortedFrequency (g₁ m)), F m +
          ∑ m ∈ s.filter (fun m => IsSortedFrequency (g₂ m)), F m +
          ∑ m ∈ s.filter (fun m => IsSortedFrequency (g₃ m)), F m +
          ∑ m ∈ s.filter (fun m => IsSortedFrequency (g₄ m)), F m +
          ∑ m ∈ s.filter (fun m => IsSortedFrequency (g₅ m)), F m := by
        simp only [Finset.sum_add_distrib, Finset.sum_filter]
    _ = 6 * ∑ m ∈ s.filter IsSortedFrequency, F m := by
        rw [e₁, e₂, e₃, e₄, e₅]; ring

/-- The box `0 < |m_i| ≤ K` is invariant under the cyclic shift. -/
theorem mem_nonzeroFrequencyBox_cycle {K : ℕ} (m : ℤ × ℤ × ℤ) :
    m ∈ nonzeroFrequencyBox K ↔ freqCycle m ∈ nonzeroFrequencyBox K := by
  simp only [mem_nonzeroFrequencyBox, freqCycle]; tauto

/-- The box `0 < |m_i| ≤ K` is invariant under the reflection. -/
theorem mem_nonzeroFrequencyBox_flip {K : ℕ} (m : ℤ × ℤ × ℤ) :
    m ∈ nonzeroFrequencyBox K ↔ freqFlip m ∈ nonzeroFrequencyBox K := by
  simp only [mem_nonzeroFrequencyBox, freqFlip, abs_neg, ne_eq, neg_eq_zero]; tauto

/-- **Symmetrisation.** `Σ_{0<|m_i|≤K} |I_m| ≤ 6 Σ_{0<|m_i|≤K, |m₁|≤|m₂|≤|m₃|} |I_m|`. -/
theorem sum_norm_cubicTerm_le_six_sorted (w : CGLRealSmoothBump) (W : Finset ℝ) (N : ℝ) (K : ℕ) :
    ∑ m ∈ nonzeroFrequencyBox K, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ ≤
      6 * ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
        ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ :=
  sum_le_six_mul_sum_sorted _ _ (fun _ => norm_nonneg _) mem_nonzeroFrequencyBox_cycle
    mem_nonzeroFrequencyBox_flip
    (fun m => by simp only [freqCycle]; rw [cubicTerm_cycle])
    (fun m => by simp only [freqFlip]; exact norm_cubicTerm_flip w W N _ _ _)

end

end RHTower.GuthMaynard
