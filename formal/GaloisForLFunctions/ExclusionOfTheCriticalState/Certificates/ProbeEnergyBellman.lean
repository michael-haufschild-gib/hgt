import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.FiniteBellman
import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi

/-!
# Bellman certificates for finite Weil probe matrices

Adding one node to a quadratic form adds its diagonal and both cross terms.
These shell costs turn finite probe energies into descending-chain values.
The stopped-chain certificate therefore bounds actual Weil energies and gives
complete certificates for either strict sign. No positivity of the kernel is
assumed. The explicit symbol formula applies to every node `5 + |p n|`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeBellman

open FiniteBellman
noncomputable section

/-- Quadratic form on the first `n` nodes of an arbitrary real kernel. -/
def quadratic (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c i * c j * K i j

/-- The diagonal and both cross terms introduced by one new node. -/
def shell (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  c n * c n * K n n +
    ∑ j ∈ Finset.range n, (c n * c j * K n j + c j * c n * K j n)

theorem quadratic_succ (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    quadratic K c (n + 1) = quadratic K c n + shell K c n := by
  simp only [quadratic, shell, Finset.sum_range_succ, Finset.sum_add_distrib]
  ring

/-- Finite quadratic energies are exactly accumulated shell costs. -/
theorem value_shell (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) :
    value (shell K c) = quadratic K c := by
  funext n
  induction n with
  | zero => simp [quadratic]
  | succ n ih => rw [value_succ, quadratic_succ, ih]

/-- An arbitrary proposed prefix-energy sequence gives rigorous two-sided bounds. -/
theorem quadratic_interval (K : ℕ → ℕ → ℝ) (c W : ℕ → ℝ) (n : ℕ) :
    W n - certificate (shell K c) W n ≤ quadratic K c n ∧
      quadratic K c n ≤ W n + certificate (shell K c) W n := by
  simpa only [value_shell] using value_mem_certificate_interval (shell K c) W n

private theorem certificate_quadratic_zero (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    certificate (shell K c) (quadratic K c) n = 0 := by
  have h0 : quadratic K c 0 = 0 := by simp [quadratic]
  have hr : residual (shell K c) (quadratic K c) = 0 := by
    funext j
    simp only [FiniteBellman.residual, quadratic_succ, Pi.zero_apply]
    ring
  simp only [certificate, h0, hr, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero]

/-- A negative quadratic form has a residual certificate, and every such certificate is sound. -/
theorem negative_certificate_iff (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    (∃ W : ℕ → ℝ, W n + certificate (shell K c) W n < 0) ↔ quadratic K c n < 0 := by
  constructor
  · rintro ⟨W, hW⟩
    exact lt_of_le_of_lt (quadratic_interval K c W n).2 hW
  · intro h
    refine ⟨quadratic K c, ?_⟩
    simpa only [certificate_quadratic_zero, add_zero] using h

/-- Positive energies admit the corresponding complete lower certificate. -/
theorem positive_certificate_iff (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    (∃ W : ℕ → ℝ, 0 < W n - certificate (shell K c) W n) ↔ 0 < quadratic K c n := by
  constructor
  · rintro ⟨W, hW⟩
    exact lt_of_lt_of_le hW (quadratic_interval K c W n).1
  · intro h
    refine ⟨quadratic K c, ?_⟩
    simpa only [certificate_quadratic_zero, sub_zero] using h

/-- The actual Weil kernel on probes whose exponents always lie in the energy domain. -/
def weilKernel (p : ℕ → ℝ) (i j : ℕ) : ℝ :=
  bareMixedEnergy (probe (5 + |p i|)) (probe (5 + |p j|))

/-- Symbol values provide the shell costs without an assumption about RH. -/
theorem weil_shell_symbol (p c : ℕ → ℝ) (n : ℕ) :
    shell (weilKernel p) c n =
      c n ^ 2 * (probeSymbol (5 + |p n|) / (5 + |p n|)) +
      2 * c n * ∑ j ∈ Finset.range n,
        c j * ((probeSymbol (5 + |p n|) + probeSymbol (5 + |p j|)) /
          ((5 + |p n|) + (5 + |p j|))) := by
  have hp (i : ℕ) : (1 / 2 : ℝ) < 5 + |p i| := by linarith [abs_nonneg (p i)]
  have he (i j : ℕ) : weilKernel p i j =
      (probeSymbol (5 + |p i|) + probeSymbol (5 + |p j|)) /
        ((5 + |p i|) + (5 + |p j|)) := bareMixedEnergy_probe (hp i) (hp j)
  unfold shell
  simp only [he, Finset.mul_sum]
  have hd : (probeSymbol (5 + |p n|) + probeSymbol (5 + |p n|)) /
      ((5 + |p n|) + (5 + |p n|)) = probeSymbol (5 + |p n|) / (5 + |p n|) := by
    have h0 : (5 : ℝ) + |p n| ≠ 0 := by positivity
    have h1 : (5 : ℝ) + |p n| + (5 + |p n|) ≠ 0 := by positivity
    field_simp <;> ring
  rw [hd]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [add_comm (probeSymbol (5 + |p j|)), add_comm (5 + |p j|)]
    ring

/-- Every finite Weil probe energy is recovered from arbitrary initial data. -/
theorem weil_iteration_exact (p c W : ℕ → ℝ) (n : ℕ) :
    (step (shell (weilKernel p) c))^[n + 1] W n =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        c i * c j * bareMixedEnergy (probe (5 + |p i|)) (probe (5 + |p j|)) := by
  rw [iterate_exact, value_shell]
  rfl

#print axioms value_shell
#print axioms quadratic_interval
#print axioms negative_certificate_iff
#print axioms positive_certificate_iff
#print axioms weil_shell_symbol
#print axioms weil_iteration_exact

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeBellman
