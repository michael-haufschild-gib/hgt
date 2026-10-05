import GaloisForLFunctions.HTGeometry.RamificationSpectralFusion
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Information fusion and formation work of a ramification power formation

For probability vectors on a countable set put
`D(P‖Q) = Σ_x P(x) log(P(x)/Q(x))` (`+∞` when `P` charges a `Q`-null point or the series diverges),
`d_{Ber}(a‖b) = a log(a/b) + (1-a) log((1-a)/(1-b))`, the affinity `Σ_x √(P(x)Q(x))` and the total
variation `½ Σ_x |P(x) - Q(x)|`.

The shell laws are the Dirichlet vectors `P_{m,σ}(n) = n^{-σ}/S_m(σ)` on `A_m`; on the splitting
`A_{rm} ≃ A_m ⊔ X_{m,r}` the target law is `α P_{m,rσ}` on inherited atoms and `β Q_{m,r,σ}` on
excess
atoms, and the inherited conditional law `I_{m,r,σ}` is `P_{m,rσ}` on inherited atoms and `0` on
excess atoms (these are the atom masses of the laws on the line).

* **Theorem 5.1 (exact information chain)**: all divergences are finite and
  `D(P_{rm,σ}‖P_{rm,τ}) = d_{Ber}(α_σ‖α_τ) + α_σ D(P_{m,rσ}‖P_{m,rτ}) + β_σ D(Q_σ‖Q_τ)`.
* **Theorem 5.2 (work, affinity, total variation)**: `W = D(I‖P_{rm,σ}) = -log α > 0`,
  `D(P_{rm,σ}‖I) = +∞`, `Aff(P_{rm,σ}, I) = √α`, `TV(P_{rm,σ}, I) = β`.
* **Theorem 6.1**: `α_{m,sr}(σ) = α_{rm,s}(σ) α_{m,r}(sσ)` and
  `W_{m,sr}(σ) = W_{rm,s}(σ) + W_{m,r}(sσ)`,
  with the three-layer refinement `S_{srm}(σ) = S_m(srσ) + C_{m,r}(sσ) + C_{rm,s}(σ)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower

/-! ### Discrete divergences -/

section Divergence

variable {α : Type*}

/-- The summand `P(x) log(P(x)/Q(x))` of the divergence. -/
def klTerm (p q : α → ℝ) (x : α) : ℝ := p x * Real.log (p x / q x)

open scoped Classical in
/-- `D(P‖Q) = Σ_x P(x) log(P(x)/Q(x))`, with value `+∞` when `P` charges a `Q`-null point or the
series diverges. -/
def klDiv (p q : α → ℝ) : EReal :=
  if (∀ x, q x = 0 → p x = 0) ∧ Summable (klTerm p q) then ((∑' x, klTerm p q x : ℝ) : EReal)
  else ⊤

/-- The Bernoulli divergence `d_{Ber}(a‖b)`. -/
def berDiv (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- The affinity `Σ_x √(P(x) Q(x))`. -/
def affinity (p q : α → ℝ) : ℝ := ∑' x, Real.sqrt (p x * q x)

/-- The total variation `½ Σ_x |P(x) - Q(x)|`. -/
def totalVariation (p q : α → ℝ) : ℝ := (∑' x, |p x - q x|) / 2

theorem klDiv_of_summable {p q : α → ℝ} (hac : ∀ x, q x = 0 → p x = 0)
    (hs : Summable (klTerm p q)) : klDiv p q = ((∑' x, klTerm p q x : ℝ) : EReal) := by
  classical
  rw [klDiv, if_pos ⟨hac, hs⟩]

theorem klDiv_eq_top {p q : α → ℝ} {x : α} (hq : q x = 0) (hp : p x ≠ 0) : klDiv p q = ⊤ := by
  classical
  rw [klDiv, if_neg fun h => hp (h.1 x hq)]

end Divergence

theorem tsum_split {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (g : κ → ℝ)
    (h1 : Summable fun i => g (e.symm (Sum.inl i)))
    (h2 : Summable fun x => g (e.symm (Sum.inr x))) :
    ∑' k, g k = ∑' i, g (e.symm (Sum.inl i)) + ∑' x, g (e.symm (Sum.inr x)) := by
  rw [← e.symm.tsum_eq g]
  exact Summable.tsum_sum h1 h2

theorem summable_split {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ) (g : κ → ℝ)
    (h1 : Summable fun i => g (e.symm (Sum.inl i))) (h2 : Summable fun x => g (e.symm (Sum.inr x))) :
    Summable g :=
  e.symm.summable_iff.1 (Summable.sum _ h1 h2)

/-! ### Dirichlet laws on a set of integers -/

section Dirichlet

variable {α : Type*} {f : α → ℕ}

/-- `Z(σ) = Σ_a f(a)^{-σ}`. -/
def dirichletSum (f : α → ℕ) (σ : ℝ) : ℝ := ∑' a, ((f a : ℕ) : ℝ) ^ (-σ)

/-- The Dirichlet law `f(a)^{-σ}/Z(σ)`. -/
def dirichletProb (f : α → ℕ) (σ : ℝ) (a : α) : ℝ := ((f a : ℕ) : ℝ) ^ (-σ) / dirichletSum f σ

variable (hf : Function.Injective f) (hf2 : ∀ a, 2 ≤ f a)
include hf hf2

omit hf in
theorem pos_f (a : α) : (0 : ℝ) < f a := by exact_mod_cast (show 0 < f a by have := hf2 a; omega)

omit hf2 in
theorem summable_dirichlet {σ : ℝ} (hσ : 1 < σ) : Summable fun a => ((f a : ℕ) : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.2 (by linarith)).comp_injective hf

theorem summable_dirichlet_log {σ : ℝ} (hσ : 1 < σ) :
    Summable fun a => ((f a : ℕ) : ℝ) ^ (-σ) * Real.log (f a) := by
  have h := (summable_abs_log_natCast_pow_mul_rpow_neg 1 σ hσ).comp_injective hf
  refine Summable.of_norm_bounded h fun a => ?_
  simp only [Function.comp_apply, pow_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (pos_f hf2 a) _)]
  rw [mul_comm]

theorem dirichletSum_pos [Nonempty α] {σ : ℝ} (hσ : 1 < σ) : 0 < dirichletSum f σ :=
  (summable_dirichlet hf hσ).tsum_pos (fun a => (Real.rpow_pos_of_pos (pos_f hf2 a) _).le)
    (Classical.arbitrary α) (Real.rpow_pos_of_pos (pos_f hf2 _) _)

theorem dirichletProb_pos [Nonempty α] {σ : ℝ} (hσ : 1 < σ) (a : α) :
    0 < dirichletProb f σ a :=
  div_pos (Real.rpow_pos_of_pos (pos_f hf2 a) _) (dirichletSum_pos hf hf2 hσ)

omit hf2 in
theorem summable_dirichletProb {σ : ℝ} (hσ : 1 < σ) : Summable (dirichletProb f σ) :=
  (summable_dirichlet hf hσ).div_const _

theorem tsum_dirichletProb [Nonempty α] {σ : ℝ} (hσ : 1 < σ) : ∑' a, dirichletProb f σ a = 1 := by
  rw [show (fun a => dirichletProb f σ a) = fun a => ((f a : ℕ) : ℝ) ^ (-σ) / dirichletSum f σ
    from rfl, tsum_div_const]
  exact div_self (dirichletSum_pos hf hf2 hσ).ne'

/-- `log(P_σ(a)/P_τ(a)) = (τ - σ) log f(a) + log(Z(τ)/Z(σ))`. -/
theorem log_dirichletProb_div [Nonempty α] {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (a : α) :
    Real.log (dirichletProb f σ a / dirichletProb f τ a) =
      (τ - σ) * Real.log (f a) + Real.log (dirichletSum f τ / dirichletSum f σ) := by
  have hfa := pos_f hf2 a
  have hZσ := dirichletSum_pos hf hf2 hσ
  have hZτ := dirichletSum_pos hf hf2 hτ
  rw [dirichletProb, dirichletProb, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hZσ.ne', Real.log_div (by positivity) hZτ.ne',
    Real.log_div hZτ.ne' hZσ.ne', Real.log_rpow hfa, Real.log_rpow hfa]
  ring

theorem summable_dirichlet_kl [Nonempty α] {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    Summable (klTerm (dirichletProb f σ) (dirichletProb f τ)) := by
  show Summable fun a => dirichletProb f σ a * Real.log (dirichletProb f σ a / dirichletProb f τ a)
  simp_rw [log_dirichletProb_div hf hf2 hσ hτ, mul_add]
  refine Summable.add ?_ ((summable_dirichletProb hf hσ).mul_right _)
  refine (((summable_dirichlet_log hf hf2 hσ).div_const (dirichletSum f σ)).mul_left
    (τ - σ)).congr fun a => ?_
  rw [dirichletProb]
  ring

/-- Dirichlet divergences are finite. -/
theorem klDiv_dirichlet [Nonempty α] {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    klDiv (dirichletProb f σ) (dirichletProb f τ) =
      ((∑' a, klTerm (dirichletProb f σ) (dirichletProb f τ) a : ℝ) : EReal) :=
  klDiv_of_summable (fun a h => absurd h (dirichletProb_pos hf hf2 hτ a).ne')
    (summable_dirichlet_kl hf hf2 hσ hτ)

end Dirichlet

/-! ### The shell laws -/

variable {m r : ℕ}

/-- The shell law `P_{m,σ}(n) = n^{-σ}/S_m(σ)` on `A_m`. -/
abbrev shellProb (m : ℕ) (σ : ℝ) : EulerShell m → ℝ := dirichletProb (fun n => (n : ℕ)) σ

/-- The excess law `Q_{m,r,σ}(N) = N^{-σ}/C_{m,r}(σ)` on `X_{m,r}`. -/
abbrev excessProb (m r : ℕ) (σ : ℝ) : ExcessShell m r → ℝ :=
  dirichletProb (fun N => ((N : EulerShell (r * m)) : ℕ)) σ

/-- The inherited conditional law `I_{m,r,σ}` on `A_{rm}`: `P_{m,rσ}` on inherited atoms, `0` on
excess atoms. -/
def inheritedProb (m r : ℕ) (hr : r ≠ 0) (σ : ℝ) (N : EulerShell (r * m)) : ℝ :=
  Sum.elim (shellProb m (r * σ)) 0 (shellSplit hr N)

theorem shell_injective (m : ℕ) : Function.Injective fun n : EulerShell m => (n : ℕ) :=
  Subtype.val_injective

theorem shell_two_le (m : ℕ) (n : EulerShell m) : 2 ≤ (n : ℕ) := n.2.1

theorem excess_injective (m r : ℕ) :
    Function.Injective fun N : ExcessShell m r => ((N : EulerShell (r * m)) : ℕ) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem excess_two_le (m r : ℕ) (N : ExcessShell m r) : 2 ≤ ((N : EulerShell (r * m)) : ℕ) :=
  N.1.2.1

theorem shellProb_eq (m : ℕ) (σ : ℝ) (n : EulerShell m) :
    shellProb m σ n = ((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ := rfl

theorem excessProb_eq (m r : ℕ) (σ : ℝ) (N : ExcessShell m r) :
    excessProb m r σ N = ((N : ℕ) : ℝ) ^ (-σ) / excessSum m r σ := rfl

theorem nonempty_shell (hm : 1 ≤ m) : Nonempty (EulerShell m) :=
  ⟨⟨2 ^ m, Nat.one_lt_two_pow (by omega), shellIndicator_two_pow m⟩⟩

theorem nonempty_excess (hm : 1 ≤ m) (hr : 2 ≤ r) : Nonempty (ExcessShell m r) :=
  ⟨excessWitness (by omega) hr⟩

section Laws

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
include hm hr hσ

/-- On an inherited atom `k^r` the target law is `α P_{m,rσ}(k)`. -/
theorem shellProb_inl (k : EulerShell m) :
    shellProb (r * m) σ ((shellSplit (by omega : r ≠ 0)).symm (Sum.inl k)) =
      survival m r σ * shellProb m (r * σ) k := by
  have hS := eulerShellSum_pos (one_le_mul_m hm hr) hσ
  have hSm := eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ)
  rw [shellProb_eq, shellProb_eq, shellSplit_symm_inl, rpow_shellPow, survival]
  field_simp

/-- On an excess atom the target law is `β Q_{m,r,σ}`. -/
theorem shellProb_inr (N : ExcessShell m r) :
    shellProb (r * m) σ ((shellSplit (by omega : r ≠ 0)).symm (Sum.inr N)) =
      excessFraction m r σ * excessProb m r σ N := by
  have hS := eulerShellSum_pos (one_le_mul_m hm hr) hσ
  have hC := excessSum_pos (m := m) (by omega) hr hσ
  rw [shellProb_eq, excessProb_eq, shellSplit_symm_inr, excessFraction]
  field_simp

end Laws

/-! ### Theorem 5.1: the exact information chain -/

section Chain

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ)
include hm hr hσ hτ

omit hm hr hσ hτ in
theorem log_mul_div_mul {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.log (a * b / (c * d)) = Real.log (a / c) + Real.log (b / d) := by
  rw [mul_div_mul_comm, Real.log_mul (by positivity) (by positivity)]

/-- **Theorem 5.1 `(FE.30)`**: every divergence is finite and
`D(P_{rm,σ}‖P_{rm,τ}) = d_{Ber}(α_σ‖α_τ) + α_σ D(P_{m,rσ}‖P_{m,rτ}) + β_σ D(Q_σ‖Q_τ)`. -/
theorem information_chain :
    ∑' N, klTerm (shellProb (r * m) σ) (shellProb (r * m) τ) N =
      berDiv (survival m r σ) (survival m r τ) +
        survival m r σ * ∑' k, klTerm (shellProb m (r * σ)) (shellProb m (r * τ)) k +
        excessFraction m r σ * ∑' N, klTerm (excessProb m r σ) (excessProb m r τ) N := by
  haveI := nonempty_shell hm
  haveI := nonempty_excess hm hr
  have hr0 : r ≠ 0 := by omega
  have hrσ := one_lt_mul_of_two_le hr hσ
  have hrτ := one_lt_mul_of_two_le hr hτ
  have hασ := survival_pos hm hr hσ
  have hατ := survival_pos hm hr hτ
  have hβσ := excessFraction_pos hm hr hσ
  have hβτ := excessFraction_pos hm hr hτ
  have hP := dirichletProb_pos (shell_injective m) (shell_two_le m) (σ := r * σ) hrσ
  have hP' := dirichletProb_pos (shell_injective m) (shell_two_le m) (σ := r * τ) hrτ
  have hQ := dirichletProb_pos (excess_injective m r) (excess_two_le m r) hσ
  have hQ' := dirichletProb_pos (excess_injective m r) (excess_two_le m r) hτ
  have hsP := summable_dirichletProb (shell_injective m) hrσ
  have hsQ := summable_dirichletProb (excess_injective m r) hσ
  have hklP := summable_dirichlet_kl (shell_injective m) (shell_two_le m) hrσ hrτ
  have hklQ := summable_dirichlet_kl (excess_injective m r) (excess_two_le m r) hσ hτ
  have hinl : ∀ k, klTerm (shellProb (r * m) σ) (shellProb (r * m) τ)
      ((shellSplit hr0).symm (Sum.inl k)) =
      survival m r σ * Real.log (survival m r σ / survival m r τ) * shellProb m (r * σ) k +
        survival m r σ * klTerm (shellProb m (r * σ)) (shellProb m (r * τ)) k := fun k => by
    rw [klTerm, klTerm, shellProb_inl hm hr hσ, shellProb_inl hm hr hτ,
      log_mul_div_mul hασ (hP k) hατ (hP' k)]
    ring
  have hinr : ∀ N, klTerm (shellProb (r * m) σ) (shellProb (r * m) τ)
      ((shellSplit hr0).symm (Sum.inr N)) =
      excessFraction m r σ * Real.log (excessFraction m r σ / excessFraction m r τ) *
          excessProb m r σ N +
        excessFraction m r σ * klTerm (excessProb m r σ) (excessProb m r τ) N := fun N => by
    rw [klTerm, klTerm, shellProb_inr hm hr hσ, shellProb_inr hm hr hτ,
      log_mul_div_mul hβσ (hQ N) hβτ (hQ' N)]
    ring
  have hs1 := (hsP.mul_left (survival m r σ * Real.log (survival m r σ / survival m r τ))).add
    (hklP.mul_left (survival m r σ))
  have hs2 := (hsQ.mul_left (excessFraction m r σ *
    Real.log (excessFraction m r σ / excessFraction m r τ))).add
      (hklQ.mul_left (excessFraction m r σ))
  rw [tsum_split (shellSplit hr0) _ (hs1.congr fun k => (hinl k).symm)
    (hs2.congr fun N => (hinr N).symm), tsum_congr hinl, tsum_congr hinr]
  rw [Summable.tsum_add (hsP.mul_left _) (hklP.mul_left _),
    Summable.tsum_add (hsQ.mul_left _) (hklQ.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, tsum_mul_left,
    tsum_dirichletProb (shell_injective m) (shell_two_le m) hrσ,
    tsum_dirichletProb (excess_injective m r) (excess_two_le m r) hσ, berDiv]
  have h1 := survival_add_excessFraction hm hr hσ
  have h2 := survival_add_excessFraction hm hr hτ
  rw [show 1 - survival m r σ = excessFraction m r σ by linarith,
    show 1 - survival m r τ = excessFraction m r τ by linarith]
  ring

/-- The four divergences of Theorem 5.1 are finite. -/
theorem information_chain_finite :
    klDiv (shellProb (r * m) σ) (shellProb (r * m) τ) ≠ ⊤ ∧
      klDiv (shellProb m (r * σ)) (shellProb m (r * τ)) ≠ ⊤ ∧
      klDiv (excessProb m r σ) (excessProb m r τ) ≠ ⊤ := by
  haveI := nonempty_shell hm
  haveI := nonempty_excess hm hr
  haveI := nonempty_shell (one_le_mul_m hm hr)
  refine ⟨?_, ?_, ?_⟩
  · rw [klDiv_dirichlet (shell_injective _) (shell_two_le _) hσ hτ]; exact EReal.coe_ne_top _
  · rw [klDiv_dirichlet (shell_injective _) (shell_two_le _) (one_lt_mul_of_two_le hr hσ)
      (one_lt_mul_of_two_le hr hτ)]
    exact EReal.coe_ne_top _
  · rw [klDiv_dirichlet (excess_injective _ _) (excess_two_le _ _) hσ hτ]
    exact EReal.coe_ne_top _

end Chain

/-! ### Theorem 5.2: work, affinity and total variation -/

/-- The formation work `W_{m,r}(σ) = -log α_{m,r}(σ)`. -/
def formationWork (m r : ℕ) (σ : ℝ) : ℝ := -Real.log (survival m r σ)

section Work

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
include hm hr hσ

omit hm hσ in
theorem inheritedProb_inl (k : EulerShell m) :
    inheritedProb m r (by omega) σ ((shellSplit (by omega : r ≠ 0)).symm (Sum.inl k)) =
      shellProb m (r * σ) k := by
  simp [inheritedProb]

omit hm hσ in
theorem inheritedProb_inr (N : ExcessShell m r) :
    inheritedProb m r (by omega) σ ((shellSplit (by omega : r ≠ 0)).symm (Sum.inr N)) = 0 := by
  simp [inheritedProb]

/-- **Theorem 5.2 `(FE.32)`**: `W_{m,r}(σ) = D(I_{m,r,σ}‖P_{rm,σ}) = -log α = log S_{rm}(σ) -
log S_m(rσ) > 0`. -/
theorem work_eq :
    klDiv (inheritedProb m r (by omega) σ) (shellProb (r * m) σ) =
        ((formationWork m r σ : ℝ) : EReal) ∧
      formationWork m r σ = Real.log (eulerShellSum (r * m) σ) -
        Real.log (eulerShellSum m (r * σ)) ∧ 0 < formationWork m r σ := by
  haveI := nonempty_shell hm
  haveI := nonempty_shell (one_le_mul_m hm hr)
  have hr0 : r ≠ 0 := by omega
  have hrσ := one_lt_mul_of_two_le hr hσ
  have hα := survival_pos hm hr hσ
  have hα1 := survival_lt_one hm hr hσ
  have hP := dirichletProb_pos (shell_injective m) (shell_two_le m) (σ := r * σ) hrσ
  have hT := dirichletProb_pos (shell_injective (r * m)) (shell_two_le (r * m)) hσ
  have hsP := summable_dirichletProb (shell_injective m) hrσ
  have hinl : ∀ k, klTerm (inheritedProb m r hr0 σ) (shellProb (r * m) σ)
      ((shellSplit hr0).symm (Sum.inl k)) =
      -Real.log (survival m r σ) * shellProb m (r * σ) k := fun k => by
    rw [klTerm, inheritedProb_inl hr, shellProb_inl hm hr hσ,
      div_mul_cancel_right₀ (hP k).ne', Real.log_inv]
    ring
  have hinr : ∀ N, klTerm (inheritedProb m r hr0 σ) (shellProb (r * m) σ)
      ((shellSplit hr0).symm (Sum.inr N)) = 0 := fun N => by
    rw [klTerm, inheritedProb_inr hr, zero_mul]
  have hs1 := hsP.mul_left (-Real.log (survival m r σ))
  have hs2 : Summable fun N : ExcessShell m r => (0 : ℝ) := summable_zero
  have hsum := summable_split (shellSplit hr0) (klTerm (inheritedProb m r hr0 σ)
    (shellProb (r * m) σ)) (hs1.congr fun k => (hinl k).symm) (hs2.congr fun N => (hinr N).symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [klDiv_of_summable (fun N h => absurd h (hT N).ne') hsum]
    congr 1
    rw [tsum_split (shellSplit hr0) _ (hs1.congr fun k => (hinl k).symm)
      (hs2.congr fun N => (hinr N).symm), tsum_congr hinl, tsum_congr hinr, tsum_zero, add_zero,
      tsum_mul_left, tsum_dirichletProb (shell_injective m) (shell_two_le m) hrσ, mul_one,
      formationWork]
  · rw [formationWork, survival, Real.log_div (eulerShellSum_pos hm hrσ).ne'
      (eulerShellSum_pos (one_le_mul_m hm hr) hσ).ne']
    ring
  · rw [formationWork]
    exact neg_pos.2 (Real.log_neg hα hα1)

/-- **`(FE.33)`**: the reverse divergence is infinite: the target charges the excess atoms, where
the inherited law vanishes. -/
theorem reverse_work_eq_top :
    klDiv (shellProb (r * m) σ) (inheritedProb m r (by omega) σ) = ⊤ := by
  haveI := nonempty_shell (one_le_mul_m hm hr)
  have hx := excessWitness (m := m) (by omega) hr
  refine klDiv_eq_top (x := (shellSplit (by omega : r ≠ 0)).symm (Sum.inr hx))
    (inheritedProb_inr hr hx) ?_
  exact (dirichletProb_pos (shell_injective _) (shell_two_le _) hσ _).ne'

/-- **`(FE.34)`**: `Aff(P_{rm,σ}, I_{m,r,σ}) = √α`. -/
theorem affinity_eq :
    affinity (shellProb (r * m) σ) (inheritedProb m r (by omega) σ) =
      Real.sqrt (survival m r σ) := by
  haveI := nonempty_shell hm
  have hr0 : r ≠ 0 := by omega
  have hrσ := one_lt_mul_of_two_le hr hσ
  have hα := survival_pos hm hr hσ
  have hP := dirichletProb_pos (shell_injective m) (shell_two_le m) (σ := r * σ) hrσ
  have hsP := summable_dirichletProb (shell_injective m) hrσ
  set g : EulerShell (r * m) → ℝ := fun N =>
    Real.sqrt (shellProb (r * m) σ N * inheritedProb m r hr0 σ N)
  have hinl : ∀ k, g ((shellSplit hr0).symm (Sum.inl k)) =
      Real.sqrt (survival m r σ) * shellProb m (r * σ) k := fun k => by
    simp only [g]
    rw [shellProb_inl hm hr hσ, inheritedProb_inl hr, mul_assoc, Real.sqrt_mul hα.le,
      Real.sqrt_mul_self (hP k).le]
  have hinr : ∀ N, g ((shellSplit hr0).symm (Sum.inr N)) = 0 := fun N => by
    simp only [g]
    rw [inheritedProb_inr hr, mul_zero, Real.sqrt_zero]
  have hs1 := hsP.mul_left (Real.sqrt (survival m r σ))
  have hs2 : Summable fun N : ExcessShell m r => (0 : ℝ) := summable_zero
  rw [affinity, show (fun x => Real.sqrt (shellProb (r * m) σ x * inheritedProb m r hr0 σ x)) = g
    from rfl, tsum_split (shellSplit hr0) g (hs1.congr fun k => (hinl k).symm)
    (hs2.congr fun N => (hinr N).symm), tsum_congr hinl, tsum_congr hinr, tsum_zero, add_zero,
    tsum_mul_left, tsum_dirichletProb (shell_injective m) (shell_two_le m) hrσ, mul_one]

/-- **`(FE.35)`**: `TV(P_{rm,σ}, I_{m,r,σ}) = β`. -/
theorem totalVariation_eq :
    totalVariation (shellProb (r * m) σ) (inheritedProb m r (by omega) σ) =
      excessFraction m r σ := by
  haveI := nonempty_shell hm
  haveI := nonempty_excess hm hr
  have hr0 : r ≠ 0 := by omega
  have hrσ := one_lt_mul_of_two_le hr hσ
  have hα1 := survival_lt_one hm hr hσ
  have hβ := excessFraction_pos hm hr hσ
  have hP := dirichletProb_pos (shell_injective m) (shell_two_le m) (σ := r * σ) hrσ
  have hQ := dirichletProb_pos (excess_injective m r) (excess_two_le m r) hσ
  have hsP := summable_dirichletProb (shell_injective m) hrσ
  have hsQ := summable_dirichletProb (excess_injective m r) hσ
  set g : EulerShell (r * m) → ℝ := fun N => |shellProb (r * m) σ N - inheritedProb m r hr0 σ N|
  have hinl : ∀ k, g ((shellSplit hr0).symm (Sum.inl k)) =
      (1 - survival m r σ) * shellProb m (r * σ) k := fun k => by
    simp only [g]
    rw [shellProb_inl hm hr hσ, inheritedProb_inl hr,
      show survival m r σ * shellProb m (r * σ) k - shellProb m (r * σ) k =
        -((1 - survival m r σ) * shellProb m (r * σ) k) by ring, abs_neg,
      abs_of_pos (mul_pos (by linarith) (hP k))]
  have hinr : ∀ N, g ((shellSplit hr0).symm (Sum.inr N)) =
      excessFraction m r σ * excessProb m r σ N := fun N => by
    simp only [g]
    rw [shellProb_inr hm hr hσ, inheritedProb_inr hr, sub_zero,
      abs_of_pos (mul_pos hβ (hQ N))]
  have hs1 := hsP.mul_left (1 - survival m r σ)
  have hs2 := hsQ.mul_left (excessFraction m r σ)
  rw [totalVariation, show (fun x => |shellProb (r * m) σ x - inheritedProb m r hr0 σ x|) = g
    from rfl, tsum_split (shellSplit hr0) g (hs1.congr fun k => (hinl k).symm)
    (hs2.congr fun N => (hinr N).symm), tsum_congr hinl, tsum_congr hinr, tsum_mul_left,
    tsum_mul_left, tsum_dirichletProb (shell_injective m) (shell_two_le m) hrσ,
    tsum_dirichletProb (excess_injective m r) (excess_two_le m r) hσ,
    show 1 - survival m r σ = excessFraction m r σ by
      linarith [survival_add_excessFraction hm hr hσ]]
  ring

end Work

/-! ### Theorem 6.1: composition -/

/-- **`(FE.36)`–`(FE.37)`**: the three-layer refinement of masses,
`S_{srm}(σ) = S_m(srσ) + C_{m,r}(sσ) + C_{rm,s}(σ)`. -/
theorem threeLayer_masses {s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    eulerShellSum (s * (r * m)) σ =
      eulerShellSum m (r * (s * σ)) + excessSum m r (s * σ) + excessSum (r * m) s σ := by
  have hsσ : 1 < (s : ℝ) * σ := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hs
    nlinarith
  rw [eulerShellSum_split hs hσ, eulerShellSum_split hr hsσ]

/-- **Theorem 6.1 `(FE.38)`**: multiplicative survival, `α_{m,sr}(σ) = α_{rm,s}(σ) α_{m,r}(sσ)`. -/
theorem survival_comp {s : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) (hs : 2 ≤ s) {σ : ℝ} (hσ : 1 < σ) :
    survival m (s * r) σ = survival (r * m) s σ * survival m r (s * σ) := by
  have hsσ := one_lt_mul_of_two_le hs hσ
  have h1 := eulerShellSum_pos (one_le_mul_m hm hr) hsσ
  rw [survival, survival, survival, mul_assoc s r m, div_mul_div_comm,
    mul_comm (eulerShellSum (s * (r * m)) σ), ← div_mul_div_comm, div_self h1.ne', one_mul]
  congr 2
  push_cast
  ring

/-- **Theorem 6.1 `(FE.39)`**: additive work with parameter transport,
`W_{m,sr}(σ) = W_{rm,s}(σ) + W_{m,r}(sσ)`. -/
theorem work_comp {s : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) (hs : 2 ≤ s) {σ : ℝ} (hσ : 1 < σ) :
    formationWork m (s * r) σ = formationWork (r * m) s σ + formationWork m r (s * σ) := by
  rw [formationWork, formationWork, formationWork, survival_comp hm hr hs hσ,
    Real.log_mul (survival_pos (one_le_mul_m hm hr) hs hσ).ne'
      (survival_pos hm hr (one_lt_mul_of_two_le hs hσ)).ne']
  ring

/-- Corollary 6.2, the inherited summand is the same along both refinements:
`α_{rm,s}(σ) α_{m,r}(sσ) = α_{m,sr}(σ)` multiplies the same conditional divergence
`D(P_{m,srσ}‖P_{m,srτ})`. -/
theorem inherited_summand_comp {s : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) (hs : 2 ≤ s) {σ : ℝ}
    (hσ : 1 < σ) (D : ℝ) :
    survival (r * m) s σ * (survival m r (s * σ) * D) = survival m (s * r) σ * D := by
  rw [survival_comp hm hr hs hσ, mul_assoc]

end GaloisForLFunctions.HTGeometry.FormationExcess
