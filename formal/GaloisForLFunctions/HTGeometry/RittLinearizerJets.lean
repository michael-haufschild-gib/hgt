import GaloisForLFunctions.HTGeometry.RittFirstOrderForm

/-!
# The shift acts triangularly on the jets of a linearizer

Let `τ` solve `σ τ = q · τ` in a Ritt frame, with `q` a derivation constant.  Differentiating the
linearizing equation and using the chain rule `d ∘ σ = ρ · (σ ∘ d)` expresses the shift of the
`n`-th derivative as `(q / ρ ^ n) · d^[n] τ` plus a base-linear combination of the *lower*
derivatives:

`σ (d^[n] τ) − (q / ρ ^ n) · d^[n] τ ∈ span_K {d τ, …, d^[n−1] τ}`.

This is the classical Faà di Bruno expansion of the substitution operator, stated as a membership in
the span of the lower jets so that no Bell-polynomial bookkeeping is needed: the span is stable
under the derivation up to one extra jet, and the induction step is a single application of the
chain rule.

The diagonal entry `q / ρ ^ n` is what makes the successive quotients `d^[n] τ / ((d τ)^n τ^{1−n})`
solutions of *inhomogeneous* first-order shift equations, the situation governed by the additive
rigidity of `RittShiftRigidity`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RittFrame

variable (Fr : RittFrame K L)

/-- The `K`-span of the first `n` derivatives of `τ`. -/
def jetSpan (τ : L) (n : ℕ) : Submodule K L :=
  Submodule.span K {x | ∃ j < n, x = Fr.d^[j + 1] τ}

theorem mem_jetSpan {τ : L} {j n : ℕ} (h : j < n) : Fr.d^[j + 1] τ ∈ Fr.jetSpan τ n :=
  Submodule.subset_span ⟨j, h, rfl⟩

theorem jetSpan_mono {τ : L} {m n : ℕ} (h : m ≤ n) : Fr.jetSpan τ m ≤ Fr.jetSpan τ n :=
  Submodule.span_mono fun _ ⟨j, hj, hx⟩ => ⟨j, lt_of_lt_of_le hj h, hx⟩

theorem jetSpan_zero (τ : L) : Fr.jetSpan τ 0 = ⊥ := by
  rw [jetSpan, show {x : L | ∃ j < 0, x = Fr.d^[j + 1] τ} = (∅ : Set L) by
    ext x; simp]
  exact Submodule.span_empty

/-- The derivation carries the span of the first `n` jets into the span of the first `n + 1`. -/
theorem d_mem_jetSpan_succ {τ : L} {n : ℕ} {x : L} (hx : x ∈ Fr.jetSpan τ n) :
    Fr.d x ∈ Fr.jetSpan τ (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [← Function.iterate_succ_apply' Fr.d]
      exact Fr.mem_jetSpan (by omega)
  | zero => rw [Fr.d_zero]; exact Submodule.zero_mem _
  | add y z hy hz ihy ihz => rw [Fr.d_add]; exact Submodule.add_mem _ ihy ihz
  | smul a y hy ihy =>
      have hsmul : Fr.d (a • y) = (Fr.dK a) • y + a • Fr.d y := by
        rw [Algebra.smul_def, Fr.d_mul, Fr.d_base, Algebra.smul_def, Algebra.smul_def]
      rw [hsmul]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Fr.jetSpan_mono (Nat.le_succ n) hy))
        (Submodule.smul_mem _ _ ihy)

/-- **Triangularity of the shift on the jets of a linearizer.**  The shift of the `(n+1)`-st
derivative is `q / ρ ^ (n+1)` times itself, modulo the span of the lower derivatives. -/
theorem shift_jet_sub_mem_jetSpan {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    ∀ n : ℕ, Fr.σ (Fr.d^[n + 1] τ) - algebraMap K L (q / Fr.ρ ^ (n + 1)) * Fr.d^[n + 1] τ
      ∈ Fr.jetSpan τ n
  | 0 => by
      have h := Fr.sigma_d_eq_of_shift hqconst hshift
      have hg : Fr.σ (Fr.d^[0 + 1] τ)
          - algebraMap K L (q / Fr.ρ ^ (0 + 1)) * Fr.d^[0 + 1] τ = 0 := by
        show Fr.σ (Fr.d τ) - algebraMap K L (q / Fr.ρ ^ (1 : ℕ)) * Fr.d τ = 0
        rw [pow_one, h, sub_self]
      rw [hg]
      exact Submodule.zero_mem _
  | (n + 1) => by
      have hρL : algebraMap K L Fr.ρ ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne
      set v : L := Fr.σ (Fr.d^[n + 1] τ)
        - algebraMap K L (q / Fr.ρ ^ (n + 1)) * Fr.d^[n + 1] τ with hv
      have hvmem : v ∈ Fr.jetSpan τ n :=
        shift_jet_sub_mem_jetSpan hqconst hshift n
      have hexp : Fr.σ (Fr.d^[n + 1] τ)
          = algebraMap K L (q / Fr.ρ ^ (n + 1)) * Fr.d^[n + 1] τ + v := by
        rw [hv]; ring
      have hderiv := congrArg Fr.d hexp
      rw [Fr.chain, Fr.d_add, Fr.d_mul, Fr.d_base] at hderiv
      rw [← Function.iterate_succ_apply' Fr.d] at hderiv
      have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
      have e1 : algebraMap K L Fr.ρ * algebraMap K L (q / Fr.ρ ^ (n + 2))
          = algebraMap K L (q / Fr.ρ ^ (n + 1)) := by
        rw [← map_mul]
        congr 1
        rw [pow_succ]
        field_simp
      have e2 : algebraMap K L Fr.ρ * algebraMap K L (Fr.ρ)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ Fr.ρ_ne, map_one]
      have hkey : Fr.σ (Fr.d^[n + 2] τ)
          - algebraMap K L (q / Fr.ρ ^ (n + 2)) * Fr.d^[n + 2] τ
          = algebraMap K L (Fr.ρ)⁻¹ *
              (algebraMap K L (Fr.dK (q / Fr.ρ ^ (n + 1))) * Fr.d^[n + 1] τ + Fr.d v) := by
        refine mul_left_cancel₀ hρL ?_
        linear_combination hderiv - Fr.d^[n + 2] τ * e1
          - (algebraMap K L (Fr.dK (q / Fr.ρ ^ (n + 1))) * Fr.d^[n + 1] τ + Fr.d v) * e2
      rw [hkey, ← Algebra.smul_def]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ (d_mem_jetSpan_succ Fr hvmem))
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (mem_jetSpan Fr (Nat.lt_succ_self n))

end RittFrame

end GaloisForLFunctions.HTGeometry
