/-
# The universal cover of every escape level, by an explicit √-branch tower

For the connected case (critical value `c` never escapes: `c ∉ escapeLevel c n` for all `n`), the
half-plane `H = exp⁻¹(escapeOpen c) = {Re t > log R}` is the universal cover of *every* escape level
`escapeLevel c n`, via the tower

  `ρ₀ = exp`,   `ρ_{n+1} = √(ρ_n − c)`   (a single-valued branch, since `H` is simply connected),

which satisfies `f ∘ ρ_{n+1} = ρ_n` and hence `f^[n] ∘ ρ_n = exp`. Each `ρ_n` is analytic on `H` and
lands in `escapeLevel c n`. This is the concrete geometric handle that makes `π₁(escapeLevel c n) ≅ ℤ`
provable without any covering-composition theory: the branches exist by `exists_analyticOnNhd_pow_eq`
on the simply-connected `H`, and the escape-level invariant propagates because `f^[n+1] = f^[n] ∘ f`.
-/
import GaloisForLFunctions.Bottcher.AnalyticRoot
import GaloisForLFunctions.Bottcher.Pi1EscapeOpen
import GaloisForLFunctions.Bottcher.EscapeCovering

open Topology
open Classical

namespace Bottcher

/-- The covering half-plane `H = exp⁻¹(escapeOpen c)`. -/
def coverPlane (c : ℂ) : Set ℂ := Complex.exp ⁻¹' (escapeOpen c)

theorem isOpen_coverPlane (c : ℂ) : IsOpen (coverPlane c) :=
  (isOpen_escapeOpen c).preimage Complex.continuous_exp

theorem isSimplyConnected_coverPlane (c : ℂ) : IsSimplyConnected (coverPlane c) :=
  Bottcher.simplyConnected_preimage_exp_escapeOpen c

/-- A single-valued square-root branch of `g` on the simply-connected `H` (junk `0` off the good
case). Exists because `H` is simply connected. -/
noncomputable def sqrtBranch (c : ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  if h : AnalyticOnNhd ℂ g (coverPlane c) ∧ ∀ t ∈ coverPlane c, g t ≠ 0 then
    (exists_analyticOnNhd_pow_eq (isSimplyConnected_coverPlane c) (isOpen_coverPlane c) h.1 h.2
      (N := 2) (by norm_num)).choose
  else 0

theorem sqrtBranch_spec (c : ℂ) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (coverPlane c)) (hgne : ∀ t ∈ coverPlane c, g t ≠ 0) :
    AnalyticOnNhd ℂ (sqrtBranch c g) (coverPlane c) ∧
      ∀ t ∈ coverPlane c, (sqrtBranch c g t) ^ (2 : ℕ) = g t := by
  have hcond : AnalyticOnNhd ℂ g (coverPlane c) ∧ ∀ t ∈ coverPlane c, g t ≠ 0 := ⟨hg, hgne⟩
  rw [sqrtBranch, dif_pos hcond]
  exact (exists_analyticOnNhd_pow_eq (isSimplyConnected_coverPlane c) (isOpen_coverPlane c)
    hcond.1 hcond.2 (N := 2) (by norm_num)).choose_spec

/-- The √-branch tower `ρ_n : H → escapeLevel c n`. -/
noncomputable def rho (c : ℂ) : ℕ → ℂ → ℂ
  | 0 => Complex.exp
  | (n + 1) => sqrtBranch c (fun t => rho c n t - c)

/-- The two propagating invariants: `ρ_n` is analytic on `H` and lands in `escapeLevel c n`. -/
theorem rho_props (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) :
    AnalyticOnNhd ℂ (rho c n) (coverPlane c) ∧
      ∀ t ∈ coverPlane c, rho c n t ∈ escapeLevel c n := by
  induction n with
  | zero =>
    refine ⟨fun z _ => analyticAt_cexp, fun t ht => ?_⟩
    rw [escapeLevel_zero]; exact ht
  | succ n ih =>
    obtain ⟨ihan, ihmem⟩ := ih
    have hgan : AnalyticOnNhd ℂ (fun t => rho c n t - c) (coverPlane c) :=
      fun z hz => (ihan z hz).sub analyticAt_const
    have hgne : ∀ t ∈ coverPlane c, (fun t => rho c n t - c) t ≠ 0 := by
      intro t ht
      have hmem : rho c n t ∈ escapeLevel c n := ihmem t ht
      refine sub_ne_zero.mpr ?_
      intro heq
      rw [heq] at hmem
      exact hc n hmem
    obtain ⟨hsan, hspow⟩ := sqrtBranch_spec c hgan hgne
    refine ⟨hsan, fun t ht => ?_⟩
    have h2 : (rho c (n + 1) t) ^ (2 : ℕ) = rho c n t - c := hspow t ht
    have hfs : quadratic c (rho c (n + 1) t) = rho c n t := by
      rw [quadratic_apply, h2]; ring
    show (quadratic c)^[n + 1] (rho c (n + 1) t) ∈ escapeOpen c
    rw [Function.iterate_succ_apply, hfs]
    exact ihmem t ht

theorem rho_analytic (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) :
    AnalyticOnNhd ℂ (rho c n) (coverPlane c) :=
  (rho_props c hc n).1

theorem rho_mem_escapeLevel (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : rho c n t ∈ escapeLevel c n :=
  (rho_props c hc n).2 t ht

@[simp] theorem rho_zero (c : ℂ) : rho c 0 = Complex.exp := rfl

/-- `ρ_{n+1}² = ρ_n − c`. -/
theorem rho_succ_sq (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : (rho c (n + 1) t) ^ (2 : ℕ) = rho c n t - c := by
  have hgan : AnalyticOnNhd ℂ (fun t => rho c n t - c) (coverPlane c) :=
    fun z hz => ((rho_analytic c hc n) z hz).sub analyticAt_const
  have hgne : ∀ t ∈ coverPlane c, (fun t => rho c n t - c) t ≠ 0 := by
    intro t ht
    have hmem : rho c n t ∈ escapeLevel c n := rho_mem_escapeLevel c hc n ht
    refine sub_ne_zero.mpr ?_
    intro heq
    rw [heq] at hmem
    exact hc n hmem
  exact (sqrtBranch_spec c hgan hgne).2 t ht

/-- The covering relation `f ∘ ρ_{n+1} = ρ_n` on `H`. -/
theorem quadratic_rho_succ (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : quadratic c (rho c (n + 1) t) = rho c n t := by
  rw [quadratic_apply, rho_succ_sq c hc n ht]; ring

/-- The tower descends to `exp`: `f^[n] ∘ ρ_n = exp` on `H`. -/
theorem iterate_quadratic_rho (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) : (quadratic c)^[n] (rho c n t) = Complex.exp t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, quadratic_rho_succ c hc n ht]
    exact ih

/-! ## The branch tower `L_n` upstairs: compatible `2ⁿ`-th roots of `bottcherCoord ∘ exp`

`L₀ = bottcherCoord c ∘ exp`, `L_{n+1} = √(L_n)`, all on the simply-connected `H`. Each `L_n` is
analytic and nowhere zero, with `L_{n+1}² = L_n`, hence `L_n^{2ⁿ} = bottcherCoord ∘ exp`. This is the
upstairs model of the level-`n` Böttcher branch: the to-be-constructed `βlev_n` on `escapeLevel c n`
is the descent of `L_n` through `ρ_n` (`βlev_n ∘ ρ_n = L_n`), and the square relation `L_{n+1}² = L_n`
becomes the supplier hypothesis `(βlev_{n+1})² = βlev_n ∘ f` of `exists_global_branch_of_sqrt_family`. -/

/-- The upstairs branch tower `L_n : H → ℂ`. -/
noncomputable def Lroot (c : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun t => bottcherCoord c (Complex.exp t)
  | (n + 1) => sqrtBranch c (Lroot c n)

/-- `L_n` is analytic on `H` and nowhere zero. -/
theorem Lroot_props (c : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (Lroot c n) (coverPlane c) ∧ ∀ t ∈ coverPlane c, Lroot c n t ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨?_, fun t _ => bottcherCoord_ne_zero c _⟩
    have hmaps : Set.MapsTo Complex.exp (coverPlane c) (escapeOpen c) := fun t ht => ht
    exact (analyticOnNhd_bottcherCoord_full c).comp (fun z _ => analyticAt_cexp) hmaps
  | succ n ih =>
    obtain ⟨ihan, ihne⟩ := ih
    obtain ⟨hsan, hspow⟩ := sqrtBranch_spec c ihan ihne
    refine ⟨hsan, fun t ht => ?_⟩
    have hsq : (Lroot c (n + 1) t) ^ (2 : ℕ) = Lroot c n t := hspow t ht
    exact fun h0 => ihne t ht (by rw [← hsq, h0]; ring)

theorem Lroot_analytic (c : ℂ) (n : ℕ) : AnalyticOnNhd ℂ (Lroot c n) (coverPlane c) :=
  (Lroot_props c n).1

theorem Lroot_ne_zero (c : ℂ) (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c) : Lroot c n t ≠ 0 :=
  (Lroot_props c n).2 t ht

@[simp] theorem Lroot_zero (c : ℂ) (t : ℂ) : Lroot c 0 t = bottcherCoord c (Complex.exp t) := rfl

/-- `L_{n+1}² = L_n` on `H` — the upstairs square relation. -/
theorem Lroot_succ_sq (c : ℂ) (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c) :
    (Lroot c (n + 1) t) ^ (2 : ℕ) = Lroot c n t :=
  (sqrtBranch_spec c (Lroot_analytic c n) (fun _ hs => Lroot_ne_zero c n hs)).2 t ht

end Bottcher
