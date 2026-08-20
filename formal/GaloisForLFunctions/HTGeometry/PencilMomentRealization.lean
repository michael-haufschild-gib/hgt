/-
# The vanishing micro-spectrum in several parameters

A diagonal operator pencil has eigenvalues that are *linear* in the parameter, so its `k`-th power
trace is a sum of `k`-th powers of linear forms.  Multiplying a one-variable root-of-unity block by
a fixed linear form therefore realises a pure homogeneous defect `c·ℓ(v)^k` with the same vanishing
lower moments and the same arbitrarily small Schatten cost, and -- crucially -- its higher moments
are again pure powers, so the residual bookkeeping of the assembly stays inside the span of `k`-th
powers.  Polarization says that span is everything, so an arbitrary homogeneous defect is reachable.

Main results:
* `clmPowSet` — the `k`-th powers of continuous linear forms.
* `exists_pencilBlock_realizing` — **one pure homogeneous defect, at arbitrarily small cost**.
* `exists_pencilSpan_realizing` — **an arbitrary combination of pure powers**.
* `exists_pencilForms_moment_realization` — **the several-variable construction `(M)`**.
-/
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentAssembly
import GaloisForLFunctions.HTGeometry.PolarizationIdentity

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The `k`-th powers of continuous linear forms on `V`. -/
def clmPowSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] (k : ℕ) : Set (V → ℂ) :=
  {f | ∃ ℓ : V →L[ℂ] ℂ, f = fun v => (ℓ v) ^ k}

theorem mem_clmPowSet (ℓ : V →L[ℂ] ℂ) (k : ℕ) :
    (fun v => (ℓ v) ^ k) ∈ clmPowSet V k := ⟨ℓ, rfl⟩

/-! ## Transporting a scalar block along a linear form -/

theorem sum_map_pow_smul (S : Multiset ℂ) (ℓ : V →L[ℂ] ℂ) (q : ℕ) (v : V) :
    (((S.map fun z : ℂ => z • ℓ).map fun m : V →L[ℂ] ℂ => (m v) ^ q).sum)
      = ((S.map fun z : ℂ => z ^ q).sum) * (ℓ v) ^ q := by
  rw [Multiset.map_map]
  have hcongr : ((fun m : V →L[ℂ] ℂ => (m v) ^ q) ∘ fun z : ℂ => z • ℓ)
      = fun z : ℂ => z ^ q * (ℓ v) ^ q := by
    funext z
    show ((z • ℓ) v) ^ q = _
    rw [smul_apply, smul_eq_mul, mul_pow]
  rw [hcongr]
  have hsplit : (S.map fun z : ℂ => z ^ q * (ℓ v) ^ q)
      = (S.map fun z : ℂ => z ^ q).map fun w => w * (ℓ v) ^ q := by
    rw [Multiset.map_map]
    rfl
  rw [hsplit, Multiset.sum_map_mul_right]
  simp

theorem sum_map_normPow_smul (S : Multiset ℂ) (ℓ : V →L[ℂ] ℂ) (p : ℕ) :
    (((S.map fun z : ℂ => z • ℓ).map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum)
      = ((S.map fun z : ℂ => ‖z‖ ^ p).sum) * ‖ℓ‖ ^ p := by
  rw [Multiset.map_map]
  have hcongr : ((fun m : V →L[ℂ] ℂ => ‖m‖ ^ p) ∘ fun z : ℂ => z • ℓ)
      = fun z : ℂ => ‖z‖ ^ p * ‖ℓ‖ ^ p := by
    funext z
    show ‖z • ℓ‖ ^ p = _
    rw [norm_smul, mul_pow]
  rw [hcongr]
  have hsplit : (S.map fun z : ℂ => ‖z‖ ^ p * ‖ℓ‖ ^ p)
      = (S.map fun z : ℂ => ‖z‖ ^ p).map fun w => w * ‖ℓ‖ ^ p := by
    rw [Multiset.map_map]
    rfl
  rw [hsplit, Multiset.sum_map_mul_right]
  simp

theorem sum_map_normPow_nonneg (S : Multiset (V →L[ℂ] ℂ)) (p : ℕ) :
    0 ≤ (S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum := by
  refine Multiset.sum_nonneg fun x hx => ?_
  obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hx
  positivity

/-- **One pure homogeneous defect, at arbitrarily small cost.** -/
theorem exists_pencilBlock_realizing {p k : ℕ} (hk : 0 < k) (hkp : k < p) (c : ℂ)
    (ℓ : V →L[ℂ] ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Multiset (V →L[ℂ] ℂ),
      (∀ q, 1 ≤ q → q < k → ∀ v, (S.map fun m => (m v) ^ q).sum = 0) ∧
      (∀ v, (S.map fun m => (m v) ^ k).sum = c * (ℓ v) ^ k) ∧
      (S.map fun m => ‖m‖ ^ p).sum < ε := by
  obtain ⟨S₀, hlow, htop, hcost⟩ :=
    exists_block_realizing hk hkp c (ε := ε / (‖ℓ‖ ^ p + 1)) (by positivity)
  refine ⟨S₀.map fun z : ℂ => z • ℓ, ?_, ?_, ?_⟩
  · intro q hq1 hqk v
    rw [sum_map_pow_smul, hlow q hq1 hqk, zero_mul]
  · intro v
    rw [sum_map_pow_smul, htop]
  · rw [sum_map_normPow_smul]
    have hnn : 0 ≤ (S₀.map fun z : ℂ => ‖z‖ ^ p).sum := by
      refine Multiset.sum_nonneg fun x hx => ?_
      obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
      positivity
    have hden : (0 : ℝ) < ‖ℓ‖ ^ p + 1 := by positivity
    calc (S₀.map fun z : ℂ => ‖z‖ ^ p).sum * ‖ℓ‖ ^ p
        ≤ (S₀.map fun z : ℂ => ‖z‖ ^ p).sum * (‖ℓ‖ ^ p + 1) := by nlinarith
      _ < (ε / (‖ℓ‖ ^ p + 1)) * (‖ℓ‖ ^ p + 1) := by
          exact mul_lt_mul_of_pos_right hcost hden
      _ = ε := div_mul_cancel₀ ε hden.ne'

/-! ## Scaling a family of forms -/

theorem sum_map_pow_const_smul (S : Multiset (V →L[ℂ] ℂ)) (b : ℂ) (q : ℕ) (v : V) :
    (((S.map fun m : V →L[ℂ] ℂ => b • m).map fun m : V →L[ℂ] ℂ => (m v) ^ q).sum)
      = b ^ q * ((S.map fun m : V →L[ℂ] ℂ => (m v) ^ q).sum) := by
  rw [Multiset.map_map]
  have hcongr : ((fun m : V →L[ℂ] ℂ => (m v) ^ q) ∘ fun m : V →L[ℂ] ℂ => b • m)
      = fun m : V →L[ℂ] ℂ => b ^ q * (m v) ^ q := by
    funext m
    show ((b • m) v) ^ q = _
    rw [smul_apply, smul_eq_mul, mul_pow]
  rw [hcongr]
  have hsplit : (S.map fun m : V →L[ℂ] ℂ => b ^ q * (m v) ^ q)
      = (S.map fun m : V →L[ℂ] ℂ => (m v) ^ q).map fun w => b ^ q * w := by
    rw [Multiset.map_map]
    rfl
  rw [hsplit, Multiset.sum_map_mul_left]
  simp

theorem sum_map_normPow_const_smul (S : Multiset (V →L[ℂ] ℂ)) (b : ℂ) (p : ℕ) :
    (((S.map fun m : V →L[ℂ] ℂ => b • m).map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum)
      = ‖b‖ ^ p * ((S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum) := by
  rw [Multiset.map_map]
  have hcongr : ((fun m : V →L[ℂ] ℂ => ‖m‖ ^ p) ∘ fun m : V →L[ℂ] ℂ => b • m)
      = fun m : V →L[ℂ] ℂ => ‖b‖ ^ p * ‖m‖ ^ p := by
    funext m
    show ‖b • m‖ ^ p = _
    rw [norm_smul, mul_pow]
  rw [hcongr]
  have hsplit : (S.map fun m : V →L[ℂ] ℂ => ‖b‖ ^ p * ‖m‖ ^ p)
      = (S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).map fun w => ‖b‖ ^ p * w := by
    rw [Multiset.map_map]
    rfl
  rw [hsplit, Multiset.sum_map_mul_left]
  simp

/-- **An arbitrary combination of pure `k`-th powers is realised**, with vanishing lower moments
and arbitrarily small Schatten cost. -/
theorem exists_pencilSpan_realizing {p k : ℕ} (hk : 0 < k) (hkp : k < p)
    {R : V → ℂ} (hR : R ∈ Submodule.span ℂ (clmPowSet V k)) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Multiset (V →L[ℂ] ℂ),
      (∀ q, 1 ≤ q → q < k → ∀ v, (S.map fun m => (m v) ^ q).sum = 0) ∧
      (∀ v, (S.map fun m => (m v) ^ k).sum = R v) ∧
      (S.map fun m => ‖m‖ ^ p).sum < ε := by
  induction hR using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨ℓ, rfl⟩ := hf
      intro ε hε
      obtain ⟨S, hlow, htop, hcost⟩ := exists_pencilBlock_realizing hk hkp 1 ℓ hε
      exact ⟨S, hlow, fun v => by rw [htop v, one_mul], hcost⟩
  | zero =>
      intro ε hε
      exact ⟨0, fun q _ _ v => by simp, fun v => by simp, by simpa using hε⟩
  | add x y hx hy ihx ihy =>
      intro ε hε
      obtain ⟨S₁, h1low, h1top, h1cost⟩ := ihx (ε / 2) (by linarith)
      obtain ⟨S₂, h2low, h2top, h2cost⟩ := ihy (ε / 2) (by linarith)
      refine ⟨S₁ + S₂, ?_, ?_, ?_⟩
      · intro q hq1 hqk v
        rw [Multiset.map_add, Multiset.sum_add, h1low q hq1 hqk v, h2low q hq1 hqk v, add_zero]
      · intro v
        rw [Multiset.map_add, Multiset.sum_add, h1top v, h2top v]
        rfl
      · rw [Multiset.map_add, Multiset.sum_add]
        linarith
  | smul a x hx ih =>
      intro ε hε
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hk
      obtain ⟨S, hlow, htop, hcost⟩ := ih (ε / (‖b‖ ^ p + 1)) (by positivity)
      refine ⟨S.map fun m => b • m, ?_, ?_, ?_⟩
      · intro q hq1 hqk v
        rw [sum_map_pow_const_smul, hlow q hq1 hqk v, mul_zero]
      · intro v
        rw [sum_map_pow_const_smul, htop v, hb]
        rfl
      · rw [sum_map_normPow_const_smul]
        have hnn : 0 ≤ (S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum := sum_map_normPow_nonneg S p
        have hden : (0 : ℝ) < ‖b‖ ^ p + 1 := by positivity
        calc ‖b‖ ^ p * (S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum
            ≤ (‖b‖ ^ p + 1) * (S.map fun m : V →L[ℂ] ℂ => ‖m‖ ^ p).sum := by nlinarith
          _ < (‖b‖ ^ p + 1) * (ε / (‖b‖ ^ p + 1)) := by
              exact mul_lt_mul_of_pos_left hcost hden
          _ = ε := mul_div_cancel₀ ε hden.ne'

/-! ## The several-variable construction `(M)` -/

theorem multiset_pow_sum_mem_span (S : Multiset (V →L[ℂ] ℂ)) (k : ℕ) :
    (fun v => (S.map fun m => (m v) ^ k).sum) ∈ Submodule.span ℂ (clmPowSet V k) := by
  refine Multiset.induction_on S ?_ ?_
  · have h0 : (fun v => ((0 : Multiset (V →L[ℂ] ℂ)).map fun m => (m v) ^ k).sum)
        = (0 : V → ℂ) := by
      funext v
      simp
    rw [h0]
    exact Submodule.zero_mem _
  · intro m S ih
    have hfun : (fun v => ((m ::ₘ S).map fun m' => (m' v) ^ k).sum)
        = (fun v => (m v) ^ k) + (fun v => (S.map fun m' => (m' v) ^ k).sum) := by
      funext v
      simp
    rw [hfun]
    exact Submodule.add_mem _ (Submodule.subset_span (mem_clmPowSet m k)) ih

/-- **The several-variable vanishing micro-spectrum construction `(M)`.**  For every prescribed
family of homogeneous defects in degrees `1, …, n` with `n < p`, each a combination of pure powers
of linear forms, and every Schatten `p` budget, there is a finite family of linear forms realising
all of them inside the budget. -/
theorem exists_pencilForms_moment_realization (p : ℕ) :
    ∀ n : ℕ, n < p → ∀ T : ℕ → V → ℂ,
      (∀ k, 1 ≤ k → k ≤ n → T k ∈ Submodule.span ℂ (clmPowSet V k)) →
      ∀ ε : ℝ, 0 < ε →
      ∃ S : Multiset (V →L[ℂ] ℂ),
        (∀ k, 1 ≤ k → k ≤ n → ∀ v, (S.map fun m => (m v) ^ k).sum = T k v) ∧
        (S.map fun m => ‖m‖ ^ p).sum < ε := by
  intro n
  induction n with
  | zero =>
      intro _ T _ ε hε
      exact ⟨0, fun k hk1 hk0 => by omega, by simpa using hε⟩
  | succ n ih =>
      intro hn T hT ε hε
      obtain ⟨S₀, hS₀mom, hS₀cost⟩ :=
        ih (by omega) T (fun k h1 h2 => hT k h1 (by omega)) (ε / 2) (by linarith)
      have hres : (fun v => T (n + 1) v - (S₀.map fun m => (m v) ^ (n + 1)).sum)
          ∈ Submodule.span ℂ (clmPowSet V (n + 1)) :=
        Submodule.sub_mem _ (hT (n + 1) (by omega) le_rfl)
          (multiset_pow_sum_mem_span S₀ (n + 1))
      obtain ⟨B, hBlow, hBtop, hBcost⟩ :=
        exists_pencilSpan_realizing (Nat.succ_pos n) hn hres (ε / 2) (by linarith)
      refine ⟨S₀ + B, ?_, ?_⟩
      · intro k hk1 hk v
        rw [Multiset.map_add, Multiset.sum_add]
        rcases Nat.lt_or_ge k (n + 1) with hlt | hge
        · rw [hBlow k hk1 hlt v, add_zero]
          exact hS₀mom k hk1 (by omega) v
        · have hkeq : k = n + 1 := by omega
          subst hkeq
          rw [hBtop v]
          ring
      · rw [Multiset.map_add, Multiset.sum_add]
        linarith

/-! ## Polarization: every product of linear forms is reachable -/

/-- **A product of `k` continuous linear forms is a combination of `k`-th powers.**  This is
polarization, and it is what makes an arbitrary homogeneous defect of degree `k` -- in particular
any `k`-th power trace of a linear operator pencil, and any element of `Sym^k(V^*)` -- reachable by
a diagonal micro-spectrum block whose eigenvalues are linear in the parameter. -/
theorem prod_clm_mem_span_clmPow {k : ℕ} (L : Fin k → (V →L[ℂ] ℂ)) :
    (fun v : V => ∏ r, L r v) ∈ Submodule.span ℂ (clmPowSet V k) := by
  classical
  have hne : ((-1 : ℂ) ^ k * (Nat.factorial k : ℂ)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast (Nat.factorial_pos k).ne'
  have hfun : (fun v : V => ∏ r, L r v)
      = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          (((-1 : ℂ) ^ k * (Nat.factorial k : ℂ))⁻¹ * (-1 : ℂ) ^ S.card) •
            (fun v : V => ((∑ r ∈ S, L r) v) ^ k) := by
    funext v
    rw [Finset.sum_apply]
    have hlin : ∀ S : Finset (Fin k), ((∑ r ∈ S, L r) v) = ∑ r ∈ S, L r v := by
      intro S
      simp
    have hpol := polarization (fun r => L r v)
    have hfac : ((Nat.factorial k : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos k).ne'
    have hgoal : (∏ r, L r v)
        = ((-1 : ℂ) ^ k * (Nat.factorial k : ℂ))⁻¹ *
          ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
            (-1 : ℂ) ^ S.card * (∑ r ∈ S, L r v) ^ k := by
      rw [hpol]
      field_simp
    rw [hgoal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hlin S]
    ring
  rw [hfun]
  refine Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨∑ r ∈ S, L r, rfl⟩

end

end GaloisForLFunctions.HTGeometry
