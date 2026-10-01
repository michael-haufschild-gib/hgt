import GaloisForLFunctions.RHTower.SmoothAFETruncation
import GaloisForLFunctions.RHTower.SteinhausModel


open Filter Topology Finset
noncomputable section
namespace RHTower

/-- The complete Gaussian-smoothed cofactor at a phase, with all positive indices retained. -/
def steinhausFullGaussianCofactor (s : ℂ) (R : ℝ) (ω : SteinhausModel.Omega) : ℂ :=
  ∑' n : ℕ, SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)

/-- Absolute Gaussian decay makes the character-weighted cofactor summable uniformly in phase. -/
theorem summable_steinhausFullGaussianCofactor {A : ℝ} (hA : 0 < A)
    {s : ℂ} (hsA : s.re < A) {R : ℝ} (hR : 0 < R) (ω : SteinhausModel.Omega) :
    Summable (fun n : ℕ => SteinhausModel.X (n + 1) ω *
      ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) := by
  have hbase := summable_smoothAFE_direct hA (s := 1 - s) hR
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  refine Summable.of_norm_bounded hbase.norm fun n => ?_
  simp only [norm_mul, SteinhausModel.norm_X, one_mul, show -(1 - s) = s - 1 by ring, le_refl]

/-- Every Gaussian cofactor tail has an arbitrary power bound, uniformly over all phases. -/
theorem exists_norm_steinhausFullGaussianCofactor_sub_head_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (R : ℝ), 0 < R → s.re < A → ∀ L : ℕ, 1 ≤ L →
      ∀ ω : SteinhausModel.Omega,
      ‖steinhausFullGaussianCofactor s R ω -
        ∑ n ∈ range L, SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
          smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ ≤
        C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) := by
  obtain ⟨C, hC, htail⟩ := exists_smoothAFE_direct_tail_le hA
  refine ⟨C, hC, fun s R hR hsA L hL ω => ?_⟩
  let a : ℕ → ℂ := fun n => SteinhausModel.X (n + 1) ω *
    ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)
  have hsum : Summable a := summable_steinhausFullGaussianCofactor hA hsA hR ω
  have hsplit := hsum.sum_add_tsum_nat_add L
  have hdiff : steinhausFullGaussianCofactor s R ω - ∑ n ∈ range L, a n =
      ∑' j : ℕ, a (j + L) := by
    change (∑' n : ℕ, a n) - _ = _
    rw [← hsplit]
    abel
  change ‖steinhausFullGaussianCofactor s R ω - ∑ n ∈ range L, a n‖ ≤ _
  rw [hdiff]
  have hsumtail : Summable (fun j : ℕ => a (j + L)) := by
    simpa only [Function.comp_def] using hsum.comp_injective (add_left_injective L)
  have hb := htail (1 - s) R hR
    (by simp only [Complex.sub_re, Complex.one_re]; linarith) L hL
  have hpow : 1 - ((1 - s).re + A) = s.re - A := by simp; ring
  have hden : (1 - s).re + A - 1 = A - s.re := by simp; ring
  rw [hpow, hden] at hb
  calc
    _ ≤ ∑' j : ℕ, ‖a (j + L)‖ := norm_tsum_le_tsum_norm hsumtail.norm
    _ = ∑' j : ℕ, ‖((j + L + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
        smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / R)‖ := by
      apply tsum_congr
      intro j
      simp only [a, norm_mul, SteinhausModel.norm_X, one_mul,
        show -(1 - s) = s - 1 by ring]
    _ ≤ _ := hb

/-- Agreement through a finite character prefix controls the full cofactor, uniformly in all
later phases. This is the quantitative preservation bound for Gaussian mode packets. -/
theorem exists_norm_steinhausFullGaussianCofactor_sub_of_prefix_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (R : ℝ), 0 < R → s.re < A → ∀ L : ℕ, 1 ≤ L →
      ∀ ω ω' : SteinhausModel.Omega,
      (∀ n : ℕ, n ≤ L → SteinhausModel.X n ω = SteinhausModel.X n ω') →
      ‖steinhausFullGaussianCofactor s R ω - steinhausFullGaussianCofactor s R ω'‖ ≤
        C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) := by
  obtain ⟨C, hC, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  refine ⟨2 * C, by positivity, fun s R hR hsA L hL ω ω' hprefix => ?_⟩
  let head : SteinhausModel.Omega → ℂ := fun u =>
    ∑ n ∈ range L, SteinhausModel.X (n + 1) u * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)
  have heq : head ω = head ω' := by
    apply sum_congr rfl
    intro n hn
    rw [hprefix (n + 1) (by have := mem_range.mp hn; omega)]
  calc
    _ = ‖(steinhausFullGaussianCofactor s R ω - head ω) -
        (steinhausFullGaussianCofactor s R ω' - head ω')‖ := by
      rw [heq]
      congr 1
      ring
    _ ≤ ‖steinhausFullGaussianCofactor s R ω - head ω‖ +
        ‖steinhausFullGaussianCofactor s R ω' - head ω'‖ := norm_sub_le _ _
    _ ≤ C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) +
        C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) :=
      add_le_add (htail s R hR hsA L hL ω) (htail s R hR hsA L hL ω')
    _ = _ := by ring

end RHTower
