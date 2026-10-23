import GaloisForLFunctions.RHTower.EstermannDeformationObstruction

/-!
# The modulus inputs are compatible with any finite zero configuration

One Euler-factor step at the prime two,
`f ↦ f − c·f(·/2)`, multiplies the Dirichlet series by `1 − c·2^{−s}` and multiplies the divisor
domination constant by `1 + ‖c‖`.  Iterating it along a list of parameters gives, for any finite
list `c₁,…,c_k`, a coefficient sequence dominated by `(∏(1+‖c_j‖))·d(N)` whose Dirichlet series is
`ζ(s)²∏_j(1 − c_j 2^{−s})`.

Choosing `c_j = 2^{s_j}` places a zero at each prescribed `s_j`.  Since the divisor domination is
the only hypothesis Weil's square-root cancellation in the modulus needs, the pair of inputs

* `‖f N‖ ≤ C·d(N)`,
* `‖∑_N f(N)S(N,b;p)N^{−s}‖ ≤ C·2√p·∑_N d(N)N^{−σ}`,

is compatible with **any** finite set of zeros at **any** abscissas.  The inputs carry no
information about the zeros whatsoever — not their location, not their number, not even a
zero-free region.
-/

open Complex

namespace RHTower

noncomputable section

/-- The undeformed divisor coefficients. -/
private def divisorCoeff (N : ℕ) : ℂ := (N.divisors.card : ℂ)

/-- One Euler-factor deformation step at the prime two. -/
def eulerTwoStep (c : ℂ) (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  f N - c * (if 2 ∣ N then f (N / 2) else 0)

/-- The deformation iterated along a list of parameters. -/
def eulerTwoTower : List ℂ → (ℕ → ℂ)
  | [] => divisorCoeff
  | c :: cs => eulerTwoStep c (eulerTwoTower cs)

/-- The domination constant of the tower. -/
def eulerTwoTowerConstant : List ℂ → ℝ
  | [] => 1
  | c :: cs => (1 + ‖c‖) * eulerTwoTowerConstant cs

theorem eulerTwoTowerConstant_nonneg : ∀ cs : List ℂ, 0 ≤ eulerTwoTowerConstant cs
  | [] => zero_le_one
  | c :: cs => by
      rw [eulerTwoTowerConstant]
      have := eulerTwoTowerConstant_nonneg cs
      have h : (0 : ℝ) ≤ 1 + ‖c‖ := by positivity
      positivity

/-- One step multiplies the divisor domination constant by `1 + ‖c‖`. -/
theorem norm_eulerTwoStep_le {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ N : ℕ, ‖f N‖ ≤ C * (N.divisors.card : ℝ)) (c : ℂ) (N : ℕ) :
    ‖eulerTwoStep c f N‖ ≤ ((1 + ‖c‖) * C) * (N.divisors.card : ℝ) := by
  classical
  have hd0 : (0 : ℝ) ≤ (N.divisors.card : ℝ) := Nat.cast_nonneg _
  have hshift : ‖(if 2 ∣ N then f (N / 2) else 0)‖ ≤ C * (N.divisors.card : ℝ) := by
    by_cases hdvd : 2 ∣ N
    · rw [if_pos hdvd]
      refine (hf (N / 2)).trans ?_
      rcases eq_or_ne N 0 with rfl | hN
      · simp
      · have hdd : N / 2 ∣ N := Nat.div_dvd_of_dvd hdvd
        have hle : ((N / 2).divisors.card : ℝ) ≤ (N.divisors.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hN hdd)
        exact mul_le_mul_of_nonneg_left hle hC
    · rw [if_neg hdvd, norm_zero]
      positivity
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have h1 := hf N
  nlinarith [h1, hshift, norm_nonneg c, hd0]

/-- The tower is dominated by the divisor function. -/
theorem norm_eulerTwoTower_le : ∀ (cs : List ℂ) (N : ℕ),
    ‖eulerTwoTower cs N‖ ≤ eulerTwoTowerConstant cs * (N.divisors.card : ℝ)
  | [], N => by
      rw [eulerTwoTower, eulerTwoTowerConstant, divisorCoeff, one_mul]
      simp
  | c :: cs, N => by
      rw [eulerTwoTower, eulerTwoTowerConstant]
      exact norm_eulerTwoStep_le (eulerTwoTowerConstant_nonneg cs)
        (norm_eulerTwoTower_le cs) c N

/-- One step multiplies the Dirichlet series by the Euler factor `1 − c·2^{−s}`. -/
theorem hasSum_eulerTwoStep {f : ℕ → ℂ} {A : ℂ} {s : ℂ} (c : ℂ)
    (h : HasSum (fun N : ℕ => f N * LSeries.term (1 : ℕ → ℂ) s N) A) :
    HasSum (fun N : ℕ => eulerTwoStep c f N * LSeries.term (1 : ℕ → ℂ) s N)
      (A * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2)) := by
  classical
  have hshift : HasSum (fun N : ℕ =>
      (if 2 ∣ N then f (N / 2) else 0) * LSeries.term (1 : ℕ → ℂ) s N)
      (LSeries.term (1 : ℕ → ℂ) s 2 * A) := by
    have hinj : Function.Injective (fun M : ℕ => 2 * M) := fun a b hab => by
      simpa using hab
    have hoff : ∀ N : ℕ, N ∉ Set.range (fun M : ℕ => 2 * M) →
        (if 2 ∣ N then f (N / 2) else 0) * LSeries.term (1 : ℕ → ℂ) s N = 0 := by
      intro N hN
      rw [if_neg, zero_mul]
      intro hd
      exact hN ⟨N / 2, (Nat.mul_div_cancel' hd)⟩
    refine (Function.Injective.hasSum_iff hinj hoff).mp ?_
    have hcomp : ∀ M : ℕ,
        ((fun N : ℕ => (if 2 ∣ N then f (N / 2) else 0) * LSeries.term (1 : ℕ → ℂ) s N) ∘
          (fun M : ℕ => 2 * M)) M
          = LSeries.term (1 : ℕ → ℂ) s 2 * (f M * LSeries.term (1 : ℕ → ℂ) s M) := by
      intro M
      simp only [Function.comp_apply, if_pos (Dvd.intro M rfl), Nat.mul_div_cancel_left M two_pos]
      rw [term_one_mul s 2 M]
      ring
    exact (h.mul_left _).congr_fun hcomp
  have hmain := h.sub (hshift.mul_left c)
  have hval : A - c * (LSeries.term (1 : ℕ → ℂ) s 2 * A)
      = A * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2) := by ring
  rw [← hval]
  refine hmain.congr_fun (fun N => ?_)
  rw [eulerTwoStep]
  ring

/-- The Dirichlet series of the tower. -/
def eulerTwoTowerFactor (s : ℂ) : List ℂ → ℂ
  | [] => 1
  | c :: cs => (eulerTwoTowerFactor s cs) * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2)

theorem eulerTwoTowerFactor_cons (s c : ℂ) (cs : List ℂ) :
    eulerTwoTowerFactor s (c :: cs)
      = eulerTwoTowerFactor s cs * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2) := rfl

theorem hasSum_eulerTwoTower {s : ℂ} (hs : 1 < s.re) : ∀ cs : List ℂ,
    HasSum (fun N : ℕ => eulerTwoTower cs N * LSeries.term (1 : ℕ → ℂ) s N)
      (riemannZeta s ^ 2 * eulerTwoTowerFactor s cs)
  | [] => by
      rw [eulerTwoTowerFactor, mul_one]
      exact (hasSum_divisorTerm hs).congr_fun (fun N => by rw [eulerTwoTower, divisorCoeff])
  | c :: cs => by
      rw [eulerTwoTower, eulerTwoTowerFactor, ← mul_assoc]
      exact hasSum_eulerTwoStep c (hasSum_eulerTwoTower hs cs)

/-- **The inputs are compatible with any finite zero configuration.**  For any list of prescribed
points `s₁,…,s_k` there is a coefficient sequence dominated by a constant times the divisor
function — hence carrying the full square-root cancellation in the modulus with that constant —
whose Dirichlet series vanishes at every `s_j`.  The abscissas are arbitrary: the two inputs give
neither a zero-free region nor any bound on the number of off-line zeros. -/
theorem exists_weil_compatible_zero_configuration (ss : List ℂ) :
    ∃ (f : ℕ → ℂ) (C : ℝ) (F : ℂ → ℂ),
      0 ≤ C ∧
      (∀ N : ℕ, ‖f N‖ ≤ C * (N.divisors.card : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re →
        HasSum (fun N : ℕ => f N * LSeries.term (1 : ℕ → ℂ) s N) (riemannZeta s ^ 2 * F s)) ∧
      (∀ s₀ ∈ ss, F s₀ = 0) := by
  classical
  refine ⟨eulerTwoTower (ss.map (fun s₀ => ((2 : ℕ) : ℂ) ^ s₀)),
    eulerTwoTowerConstant (ss.map (fun s₀ => ((2 : ℕ) : ℂ) ^ s₀)),
    fun s => eulerTwoTowerFactor s (ss.map (fun s₀ => ((2 : ℕ) : ℂ) ^ s₀)),
    eulerTwoTowerConstant_nonneg _, norm_eulerTwoTower_le _,
    fun s hs => hasSum_eulerTwoTower hs _, ?_⟩
  intro s₀ hs₀
  induction ss with
  | nil => exact absurd hs₀ (List.not_mem_nil)
  | cons a as ih =>
      simp only [List.map_cons, eulerTwoTowerFactor_cons]
      rcases List.mem_cons.mp hs₀ with h | h
      · subst h
        have h2 : ((2 : ℕ) : ℂ) ≠ 0 := by norm_num
        have hterm : LSeries.term (1 : ℕ → ℂ) s₀ 2 = (((2 : ℕ) : ℂ) ^ s₀)⁻¹ := by
          rw [LSeries.term_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)]
          simp only [Pi.one_apply, one_div]
        have hne : ((2 : ℕ) : ℂ) ^ s₀ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2)
        rw [hterm, mul_inv_cancel₀ hne, sub_self, mul_zero]
      · have hz := ih h
        simp only [] at hz
        rw [hz, zero_mul]

end

end RHTower
