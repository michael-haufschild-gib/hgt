import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave
import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityTwoTerm

/-!
# Pólya frequency order of the horizontal slice and of `ξ` at the centre

A sequence is `PF_k` when every Toeplitz minor of order `≤ k` with increasing rows and columns is
nonnegative (`PFSeq`).  This file proves the **visibility-cone law** for the slice
`g_t(x) = ξ(½ + x + it)·ξ(½ − x + it)` and for the centre function `ξ(½ + x)`.

* **Slice.**  If every zero `ρ` satisfies
  `cos (π/(k+1)) ((Im ρ − t)² + (Re ρ − ½)²) ≤ (Im ρ − t)² − (Re ρ − ½)²`, i.e.
  `|Re ρ − ½| ≤ tan (π/(2k+2)) |Im ρ − t|`, then the coefficients `c_{2n}(t)` of `g_t` in `y = x²`
  form a `PF_k` sequence (`xiSliceCoeff_pfSeq_of_cone`).  For `k = 1` this is the cone criterion
  `|Re ρ − ½| ≤ |Im ρ − t|`, and for `k = 2` the `√3`-cone.
* **Centre.**  The same law holds for the Taylor coefficients `a_n` of `ξ(½ + x) = Σ a_n x^{2n}`
  with `t = 0` (`xi_centre_pfSeq_of_cone`).  With the unconditional critical-line band below
  ordinate `√(2365/16) ≈ 12.16`, every zero satisfies the cone for `k = 37`, so `(a_n)` is `PF_37`
  (`xi_centre_pfSeq_thirtySeven`).

The mechanism is the factorization of `ξ` over its zeros.  A critical zero contributes a linear
factor `α + β y` with `α, β ≥ 0`, which is `PF` of every order (`PFSeq.twoTerm`).  An off-line orbit
with spectral offset `w = √A + i√C` contributes `C₀ ((A + C)² + 2(A − C) y + y²)`.  This is
`PF_k` exactly when its root angle `ψ = 2 arctan √(C/A)` satisfies `(k+1)ψ ≤ π`; that is the
Chebyshev threshold (`PFSeq.cosQuadratic`, `PFSeq.quadratic_of_cone`).  `PF_k` is closed under
the Cauchy product (Cauchy–Binet, `PFSeq.conv`) and under limits.  For even entire functions the
`y`-coefficients of a product are the Cauchy product of the `y`-coefficients.
-/

open Complex Filter Topology
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The `PF_k` Taylor property -/

/-- An entire function with nonnegative Taylor coefficients at `0`, vanishing odd coefficients,
and a `PF_k` sequence of even coefficients (in `y = x²`). -/
def PFTaylorAtZero (k : ℕ) (f : ℂ → ℂ) : Prop :=
  NonnegTaylorAtZero f ∧ (∀ n : ℕ, iteratedDeriv (2 * n + 1) f 0 = 0) ∧
    PFSeq k (evenTaylorRe f)

theorem PFTaylorAtZero.mul {k : ℕ} {f g : ℂ → ℂ} (hf : PFTaylorAtZero k f)
    (hg : PFTaylorAtZero k g) : PFTaylorAtZero k (f * g) := by
  refine ⟨hf.1.mul hg.1, iteratedDeriv_mul_odd_eq_zero hf.1.1 hg.1.1 hf.2.1 hg.2.1, ?_⟩
  rw [evenTaylorRe_mul hf.1 hg.1 hf.2.1]
  exact hf.2.2.conv hg.2.2

/-- **The `PF_k` Taylor property passes to locally uniform limits.** -/
theorem PFTaylorAtZero.of_tendstoLocallyUniformlyOn {k : ℕ} {ι : Type*} {l : Filter ι}
    [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ i, PFTaylorAtZero k (F i))
    (hf : Differentiable ℂ f) (h : TendstoLocallyUniformlyOn F f l Set.univ) :
    PFTaylorAtZero k f := by
  have hd : ∀ n, Tendsto (fun i => iteratedDeriv n (F i) 0) l (𝓝 (iteratedDeriv n f 0)) :=
    fun n => (tendstoLocallyUniformlyOn_iteratedDeriv (fun i => (hF i).1.1) h n).tendsto_at
      (Set.mem_univ (0 : ℂ))
  refine ⟨NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn (fun i => (hF i).1) hf h,
    fun n => ?_, ?_⟩
  · have h0 : Tendsto (fun i => iteratedDeriv (2 * n + 1) (F i) 0) l (𝓝 0) := by
      simp only [fun i => (hF i).2.1 n]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hd (2 * n + 1)) h0
  · refine PFSeq.of_tendsto (l := l) (fun i => (hF i).2.2) fun n => ?_
    unfold evenTaylorRe
    exact (Complex.continuous_re.tendsto _).comp ((hd (2 * n)).const_mul _)

/-! ## Grouping products into symmetry orbits -/

/-- A property of functions that holds for `1` and is closed under products holds for a finite
product grouped into orbits of an involution. -/
theorem prod_of_involution_of_mul {P : (ℂ → ℂ) → Prop} (hone : P fun _ => 1)
    (hmul : ∀ f g, P f → P g → P (f * g)) {α : Type*} [DecidableEq α] (σ : α → α)
    (hσ : ∀ a, σ (σ a) = a) (f : α → ℂ → ℂ) (hfix : ∀ a, σ a = a → P (f a))
    (hpair : ∀ a, σ a ≠ a → P (f a * f (σ a))) :
    ∀ S : Finset α, (∀ a ∈ S, σ a ∈ S) → P (fun x => ∏ a ∈ S, f a x) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with hE | ⟨a, ha⟩
    · subst hE
      simpa using hone
    by_cases hfa : σ a = a
    · set T := S.erase a with hT
      have hTS : T ⊂ S := Finset.erase_ssubset ha
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase] at hb ⊢
        refine ⟨fun h => hb.1 ?_, hS b hb.2⟩
        rw [← hσ b, h, hfa]
      have e : (fun x => ∏ b ∈ S, f b x) = f a * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, hT, Finset.mul_prod_erase S (fun b => f b x) ha]
      rw [e]
      exact hmul _ _ (hfix a hfa) (ih T hTS hTc)
    · have hσa : σ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hfa, hS a ha⟩
      set T := (S.erase a).erase (σ a) with hT
      have hTS : T ⊂ S :=
        (Finset.erase_ssubset hσa).trans_le (Finset.erase_subset a S)
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase, Finset.mem_erase] at hb ⊢
        exact ⟨fun h => hb.2.1 (by rw [← hσ b, h, hσ]), fun h => hb.1 (by rw [← hσ b, h]),
          hS b hb.2.2⟩
      have e : (fun x => ∏ b ∈ S, f b x) = (f a * f (σ a)) * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, Pi.mul_apply, hT,
          ← Finset.mul_prod_erase S (fun b => f b x) ha,
          ← Finset.mul_prod_erase (S.erase a) (fun b => f b x) hσa]
        ring
      rw [e]
      exact hmul _ _ (hpair a hfa) (ih T hTS hTc)

/-- A property of functions that holds for `1` and is closed under products holds for a finite
product grouped into orbits of two commuting involutions, the first without fixed points. -/
theorem prod_of_kleinOrbits_of_mul {P : (ℂ → ℂ) → Prop} (hone : P fun _ => 1)
    (hmul : ∀ f g, P f → P g → P (f * g)) {α : Type*} [DecidableEq α] (σ τ : α → α)
    (hσ : ∀ a, σ (σ a) = a) (hτ : ∀ a, τ (τ a) = a) (hστ : ∀ a, σ (τ a) = τ (σ a))
    (hσfix : ∀ a, σ a ≠ a) (f : α → ℂ → ℂ)
    (hsmall : ∀ a, (τ a = a ∨ τ a = σ a) → P (f a * f (σ a)))
    (hbig : ∀ a, τ a ≠ a → τ a ≠ σ a → P ((f a * f (σ a)) * (f (τ a) * f (σ (τ a))))) :
    ∀ S : Finset α, (∀ a ∈ S, σ a ∈ S) → (∀ a ∈ S, τ a ∈ S) →
      P (fun x => ∏ a ∈ S, f a x) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hSσ hSτ
    rcases S.eq_empty_or_nonempty with hE | ⟨a, ha⟩
    · subst hE
      simpa using hone
    have hσa : σ a ∈ S := hSσ a ha
    have hσane : σ a ≠ a := hσfix a
    by_cases hsm : τ a = a ∨ τ a = σ a
    · set T := (S.erase a).erase (σ a) with hT
      have hσaT : σ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hσane, hσa⟩
      have hTS : T ⊂ S := (Finset.erase_ssubset hσaT).trans_le (Finset.erase_subset a S)
      have hτσa : τ (σ a) = a ∨ τ (σ a) = σ a := by
        rcases hsm with h | h
        · right; rw [← hστ, h]
        · left; rw [← hστ, h, hσ]
      have hmemT : ∀ b, b ∈ T ↔ b ∈ S ∧ b ≠ a ∧ b ≠ σ a := by
        intro b
        rw [hT, Finset.mem_erase, Finset.mem_erase]
        tauto
      have hTσ : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hmemT] at hb ⊢
        refine ⟨hSσ b hb.1, fun h => hb.2.2 ?_, fun h => hb.2.1 ?_⟩
        · rw [← h, hσ]
        · rw [← hσ b, h, hσ]
      have hTτ : ∀ b ∈ T, τ b ∈ T := by
        intro b hb
        rw [hmemT] at hb ⊢
        refine ⟨hSτ b hb.1, fun h => ?_, fun h => ?_⟩
        · have : b = τ a := by rw [← h, hτ]
          rcases hsm with h' | h'
          · exact hb.2.1 (this.trans h')
          · exact hb.2.2 (this.trans h')
        · have : b = τ (σ a) := by rw [← h, hτ]
          rcases hτσa with h' | h'
          · exact hb.2.1 (this.trans h')
          · exact hb.2.2 (this.trans h')
      have e : (fun x => ∏ b ∈ S, f b x) = (f a * f (σ a)) * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, Pi.mul_apply, hT,
          ← Finset.mul_prod_erase S (fun b => f b x) ha,
          ← Finset.mul_prod_erase (S.erase a) (fun b => f b x) hσaT]
        ring
      rw [e]
      exact hmul _ _ (hsmall a hsm) (ih T hTS hTσ hTτ)
    · push Not at hsm
      obtain ⟨hτa1, hτa2⟩ := hsm
      have hτaS : τ a ∈ S := hSτ a ha
      have hστaS : σ (τ a) ∈ S := hSσ _ hτaS
      have hστ1 : σ (τ a) ≠ a := fun h => hτa2 (by rw [← hσ (τ a), h])
      have hστ2 : σ (τ a) ≠ σ a := fun h => hτa1 (by rw [← hσ (τ a), h, hσ])
      have hστ3 : σ (τ a) ≠ τ a := hσfix (τ a)
      set T := (((S.erase a).erase (σ a)).erase (τ a)).erase (σ (τ a)) with hT
      have hmemT : ∀ b, b ∈ T ↔ b ∈ S ∧ b ≠ a ∧ b ≠ σ a ∧ b ≠ τ a ∧ b ≠ σ (τ a) := by
        intro b
        rw [hT, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
        tauto
      have hTS : T ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun b hb => ((hmemT b).mp hb).1, fun h => ?_⟩
        have : a ∈ T := h ▸ ha
        exact ((hmemT a).mp this).2.1 rfl
      have hTσ : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hmemT] at hb ⊢
        obtain ⟨hbS, h1, h2, h3, h4⟩ := hb
        refine ⟨hSσ b hbS, fun h => h2 ?_, fun h => h1 ?_, fun h => h4 ?_, fun h => h3 ?_⟩
        · rw [← h, hσ]
        · rw [← hσ b, h, hσ]
        · rw [← h, hσ]
        · rw [← hσ b, h, hσ]
      have hTτ : ∀ b ∈ T, τ b ∈ T := by
        intro b hb
        rw [hmemT] at hb ⊢
        obtain ⟨hbS, h1, h2, h3, h4⟩ := hb
        refine ⟨hSτ b hbS, fun h => h3 ?_, fun h => h4 ?_, fun h => h1 ?_, fun h => h2 ?_⟩
        · rw [← h, hτ]
        · rw [hστ, ← h, hτ]
        · rw [← hτ b, h, hτ]
        · rw [← hτ b, h, ← hστ (τ a), hτ]
      have hσaS1 : σ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hσane, hσa⟩
      have hτaS2 : τ a ∈ (S.erase a).erase (σ a) :=
        Finset.mem_erase.mpr ⟨hτa2, Finset.mem_erase.mpr ⟨hτa1, hτaS⟩⟩
      have hστaS3 : σ (τ a) ∈ ((S.erase a).erase (σ a)).erase (τ a) :=
        Finset.mem_erase.mpr ⟨hστ3, Finset.mem_erase.mpr ⟨hστ2,
          Finset.mem_erase.mpr ⟨hστ1, hστaS⟩⟩⟩
      have e : (fun x => ∏ b ∈ S, f b x) =
          ((f a * f (σ a)) * (f (τ a) * f (σ (τ a)))) * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, hT,
          ← Finset.mul_prod_erase S (fun b => f b x) ha,
          ← Finset.mul_prod_erase (S.erase a) (fun b => f b x) hσaS1,
          ← Finset.mul_prod_erase ((S.erase a).erase (σ a)) (fun b => f b x) hτaS2,
          ← Finset.mul_prod_erase (((S.erase a).erase (σ a)).erase (τ a)) (fun b => f b x)
            hστaS3]
        ring
      rw [e]
      exact hmul _ _ (hbig a hτa1 hτa2) (ih T hTS hTσ hTτ)

/-! ## The factors -/

/-- The `y`-coefficients of an even quartic `c₀ + c₂x² + c₄x⁴` are `(c₀, c₂, c₄, 0, …)`. -/
theorem evenTaylorRe_evenQuartic (c0 c2 c4 : ℝ) :
    evenTaylorRe (fun x : ℂ => (c0 : ℂ) + (c2 : ℂ) * x ^ 2 + (c4 : ℂ) * x ^ 4) =
      fun n => if n = 0 then c0 else if n = 1 then c2 else if n = 2 then c4 else 0 := by
  funext n
  unfold evenTaylorRe
  rw [iteratedDeriv_evenQuartic_zero]
  rcases n with _ | _ | _ | n
  · simp
  · simp [Nat.factorial]
    ring
  · simp [Nat.factorial]
    ring
  · have ha : 2 * (n + 3) ≠ 0 := by omega
    have hb : 2 * (n + 3) ≠ 2 := by omega
    have hc : 2 * (n + 3) ≠ 4 := by omega
    simp [ha, hb, hc]

/-- An even quartic with nonnegative coefficients and a `PF_k` coefficient sequence has the `PF_k`
Taylor property. -/
theorem pfTaylorAtZero_evenQuartic {k : ℕ} {c0 c2 c4 : ℝ} (h0 : 0 ≤ c0) (h2 : 0 ≤ c2)
    (h4 : 0 ≤ c4)
    (h : PFSeq k (fun n => if n = 0 then c0 else if n = 1 then c2 else if n = 2 then c4 else 0)) :
    PFTaylorAtZero k (fun x : ℂ => (c0 : ℂ) + (c2 : ℂ) * x ^ 2 + (c4 : ℂ) * x ^ 4) := by
  refine ⟨⟨by fun_prop, fun n => ?_⟩, fun n => ?_, ?_⟩
  · rw [iteratedDeriv_evenQuartic_zero]
    have hc0 : (0 : ℂ) ≤ (c0 : ℂ) := Complex.zero_le_real.mpr h0
    have hc2 : (0 : ℂ) ≤ (c2 : ℂ) := Complex.zero_le_real.mpr h2
    have hc4 : (0 : ℂ) ≤ (c4 : ℂ) := Complex.zero_le_real.mpr h4
    refine add_nonneg (add_nonneg ?_ (mul_nonneg hc2 ?_)) (mul_nonneg hc4 ?_) <;>
      split_ifs <;> first | exact hc0 | exact le_rfl | norm_num
  · rw [iteratedDeriv_evenQuartic_zero]
    have h2' : 2 * n + 1 ≠ 2 := by omega
    have h3 : 2 * n + 1 ≠ 4 := by omega
    simp [h2', h3]
  · rw [evenTaylorRe_evenQuartic]
    exact h

/-- An even quadratic `α + βx²` with `α, β ≥ 0` is `PF_k` for every `k`. -/
theorem pfTaylorAtZero_linear (k : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    PFTaylorAtZero k (fun x : ℂ => (α : ℂ) + (β : ℂ) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4) := by
  refine pfTaylorAtZero_evenQuartic hα hβ le_rfl ?_
  convert PFSeq.twoTerm hα hβ k using 1
  funext n
  unfold twoTermSeq
  split_ifs <;> rfl

/-- A nonnegative constant is `PF_k` for every `k`. -/
theorem pfTaylorAtZero_const (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    PFTaylorAtZero k (fun _ : ℂ => (c : ℂ)) := by
  have h := pfTaylorAtZero_linear k hc le_rfl
  have e : (fun x : ℂ => (c : ℂ) + ((0 : ℝ) : ℂ) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4) =
      fun _ : ℂ => (c : ℂ) := by
    funext x
    simp
  rwa [e] at h

/-- **The quartic factor of an off-line orbit inside the `PF_k` cone.**  For `A, C ≥ 0`,
`A + C > 0` and `cos (π/(k+1)) (A + C) ≤ A − C`, `k ≥ 1`, the factor
`C₀ (x⁴ + 2(A − C) x² + (A + C)²)`, `C₀ ≥ 0`, has the `PF_k` Taylor property. -/
theorem pfTaylorAtZero_quartic_of_cone {k : ℕ} (hk : 1 ≤ k) {C₀ A C : ℝ} (hC₀ : 0 ≤ C₀)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hAC : 0 < A + C)
    (hcone : Real.cos (Real.pi / ((k : ℝ) + 1)) * (A + C) ≤ A - C) :
    PFTaylorAtZero k (fun x : ℂ => (C₀ : ℂ) * (x ^ 4 + ((2 * (A - C) : ℝ) : ℂ) * x ^ 2 +
      (((A + C) ^ 2 : ℝ) : ℂ))) := by
  have hcos0 : 0 ≤ Real.cos (Real.pi / ((k : ℝ) + 1)) := by
    apply Real.cos_nonneg_of_mem_Icc
    have hk1 : (2 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    constructor
    · have := Real.pi_pos
      have : 0 ≤ Real.pi / ((k : ℝ) + 1) := by positivity
      linarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [Real.pi_pos]
  have hAC' : C ≤ A := by nlinarith
  have e : (fun x : ℂ => (C₀ : ℂ) * (x ^ 4 + ((2 * (A - C) : ℝ) : ℂ) * x ^ 2 +
      (((A + C) ^ 2 : ℝ) : ℂ))) =
      fun x : ℂ => ((C₀ * (A + C) ^ 2 : ℝ) : ℂ) + ((C₀ * (2 * (A - C)) : ℝ) : ℂ) * x ^ 2 +
        (C₀ : ℂ) * x ^ 4 := by
    funext x
    push_cast
    ring
  rw [e]
  refine pfTaylorAtZero_evenQuartic (by positivity) (mul_nonneg hC₀ (by linarith)) hC₀ ?_
  convert (PFSeq.quadratic_of_cone hA hC hAC hcone).const_mul hC₀ using 1
  funext n
  split_ifs <;> ring

/-! ## The slice -/

/-- A critical-line copy is fixed by the Hermitian reflection `ρ ↦ 1 − ρ̄`. -/
theorem lagPartner_eq_self_of_re {q : XiZeroCopy} (h : (q.1 : ℂ).re = 1 / 2) :
    lagPartner q = q := by
  show xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q) = q
  rw [xiZeroCopyConjEquiv_eq_reflect_of_re h, xiZeroCopyReflectEquiv_apply_apply]


/-- **The `PF_k` visibility-cone law for the slice.**  If `k ≥ 1` and every zero copy satisfies
`cos (π/(k+1)) ((Im ρ − t)² + (Re ρ − ½)²) ≤ (Im ρ − t)² − (Re ρ − ½)²`, the slice product at
height `t` has the `PF_k` Taylor property. -/
theorem pfTaylorAtZero_xiSliceProduct_of_cone {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im - t) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im - t) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) :
    PFTaylorAtZero k (xiSliceProduct t) := by
  classical
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z =>
      (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image lagPartner
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, lagPartner a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · left
      rw [lagPartner_lagPartner]
      exact hb
  have hmul' := tendstoLocallyUniformlyOn_comp_index hmul hc
  set f : XiZeroCopy → ℂ → ℂ := fun q x =>
    weierstrassE1 (φm x / xiSpectralPoint q) * weierstrassE1 (φp x / xiSpectralPoint q) with hf
  have hfix : ∀ q, lagPartner q = q → PFTaylorAtZero k (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]
      simp
    have hγ : (q.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hz, h0, Complex.ofReal_zero]
    set γ := (q.1 : ℂ).im
    have e : f q = fun x : ℂ => (((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 : ℝ) : ℂ)) +
        (((Real.exp (2 * t / γ) / γ ^ 2 : ℝ) : ℂ)) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4 := by
      funext x
      simp only [hf, hz, hφm, hφp]
      rw [weierstrassE1_slice_pair hγ x]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      ring
    rw [e]
    exact pfTaylorAtZero_linear k (by positivity) (by positivity)
  have hpair : ∀ q, lagPartner q ≠ q → PFTaylorAtZero k (f q * f (lagPartner q)) := by
    intro q hne
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hzσ : xiSpectralPoint (lagPartner q) = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      rw [xiSpectralPoint_lagPartner, hz]
    have hcc0 : cc ≠ 0 := by
      intro h0
      apply hne
      apply lagPartner_eq_self_of_re
      rw [hcc] at h0
      linarith
    have e : f q * f (lagPartner q) = fun x =>
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * ((a - t) ^ 2 - cc ^ 2) : ℝ) : ℂ) * x ^ 2 +
            ((((a - t) ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext x
      simp only [Pi.mul_apply, hf, hz, hzσ, hφm, hφp]
      exact weierstrassE1_slice_reflectionPair hz0 x
    rw [e]
    have hcone' : Real.cos (Real.pi / ((k : ℝ) + 1)) * ((a - t) ^ 2 + cc ^ 2) ≤
        (a - t) ^ 2 - cc ^ 2 := by
      have h := hcone q
      have hc2 : cc ^ 2 = ((q.1 : ℂ).re - 1 / 2) ^ 2 := by rw [hcc]; ring
      rw [hc2, ha]
      exact h
    have hpos : 0 < (a - t) ^ 2 + cc ^ 2 := by
      have : 0 < cc ^ 2 := by positivity
      positivity
    exact pfTaylorAtZero_quartic_of_cone hk (by positivity) (sq_nonneg _) (sq_nonneg _) hpos
      hcone'
  have hfin : ∀ S : Finset XiZeroCopy, PFTaylorAtZero k
      (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hf]
      rw [Finset.prod_mul_distrib]
    rw [e]
    exact prod_of_involution_of_mul (by simpa using pfTaylorAtZero_const k zero_le_one)
      (fun _ _ hf hg => hf.mul hg) lagPartner lagPartner_lagPartner f hfix hpair (c S)
      (hclosed S)
  have hlim : PFTaylorAtZero k ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) :=
    PFTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'
  have e : xiSliceProduct t = (fun _ => XiC 0 * XiC 0) *
      ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) := by
    funext x
    rw [xiSliceProduct_eq_XiC]
    have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
      simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hX ((t : ℂ) - I * x), hX ((t : ℂ) + I * x)]
    ring
  have hX0 : XiC 0 * XiC 0 = (((XiC 0 * XiC 0).re : ℝ) : ℂ) := by
    have h := zero_le_XiC_zero_mul_self
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp h).2.symm]
  have hX0nn : 0 ≤ (XiC 0 * XiC 0).re := (Complex.nonneg_iff.mp zero_le_XiC_zero_mul_self).1
  rw [e, hX0]
  exact (pfTaylorAtZero_const k hX0nn).mul hlim

/-- **`PF_k` slice coefficients inside the visibility cone.**  Under the cone condition of order
`k ≥ 1` at height `t`, the real slice coefficients `c_{2n}(t)` form a `PF_k` sequence: every
Toeplitz minor of order `≤ k` with increasing rows and columns is nonnegative. -/
theorem xiSliceCoeff_pfSeq_of_cone {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im - t) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im - t) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) :
    PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) :=
  (pfTaylorAtZero_xiSliceProduct_of_cone hk hcone).2.2

/-! ## The centre -/

/-- The off-line Klein orbit at the centre: `(1 + x²/z²)(1 + x²/z̄²)` for `z = a + ci` equals
`(a² + c²)⁻² (x⁴ + 2(a² − c²) x² + (a² + c²)²)`. -/
theorem centre_offLine_factor_eq {a c : ℝ} (hz : (a : ℂ) + c * I ≠ 0) :
    (fun x : ℂ => (1 + x ^ 2 / ((a : ℂ) + c * I) ^ 2) *
      (1 + x ^ 2 / (starRingEnd ℂ ((a : ℂ) + c * I)) ^ 2)) =
      fun x : ℂ => ((1 / (a ^ 2 + c ^ 2) ^ 2 : ℝ) : ℂ) *
        (x ^ 4 + ((2 * (a ^ 2 - c ^ 2) : ℝ) : ℂ) * x ^ 2 + (((a ^ 2 + c ^ 2) ^ 2 : ℝ) : ℂ)) := by
  have hconj : starRingEnd ℂ ((a : ℂ) + c * I) = (a : ℂ) - c * I := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hz' : (a : ℂ) - c * I ≠ 0 := by rw [← hconj]; exact (map_ne_zero _).mpr hz
  have hprod : ((a : ℂ) + c * I) * ((a : ℂ) - c * I) = (a : ℂ) ^ 2 + (c : ℂ) ^ 2 := by
    linear_combination (-(c : ℂ) ^ 2) * Complex.I_sq
  have hnormc : (a : ℂ) ^ 2 + (c : ℂ) ^ 2 ≠ 0 := by
    rw [← hprod]
    exact mul_ne_zero hz hz'
  have hsum : ((a : ℂ) + c * I) ^ 2 + ((a : ℂ) - c * I) ^ 2 =
      2 * ((a : ℂ) ^ 2 - (c : ℂ) ^ 2) := by
    linear_combination (2 * (c : ℂ) ^ 2) * Complex.I_sq
  have hprod2 : ((a : ℂ) + c * I) ^ 2 * ((a : ℂ) - c * I) ^ 2 =
      ((a : ℂ) ^ 2 + (c : ℂ) ^ 2) ^ 2 := by
    rw [← mul_pow, hprod]
  have hs : ((a : ℂ) + c * I) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hd : ((a : ℂ) - c * I) ^ 2 ≠ 0 := pow_ne_zero 2 hz'
  funext x
  rw [hconj]
  calc (1 + x ^ 2 / ((a : ℂ) + c * I) ^ 2) * (1 + x ^ 2 / ((a : ℂ) - c * I) ^ 2)
      = 1 + x ^ 2 * ((((a : ℂ) + c * I) ^ 2 + ((a : ℂ) - c * I) ^ 2) /
          (((a : ℂ) + c * I) ^ 2 * ((a : ℂ) - c * I) ^ 2)) +
          x ^ 4 / (((a : ℂ) + c * I) ^ 2 * ((a : ℂ) - c * I) ^ 2) := by
        field_simp
        ring
    _ = 1 + x ^ 2 * (2 * ((a : ℂ) ^ 2 - (c : ℂ) ^ 2) / ((a : ℂ) ^ 2 + (c : ℂ) ^ 2) ^ 2) +
          x ^ 4 / ((a : ℂ) ^ 2 + (c : ℂ) ^ 2) ^ 2 := by
        rw [hsum, hprod2]
    _ = _ := by
        push_cast
        field_simp
        ring

/-- **The `PF_k` visibility-cone law at the centre.**  If `k ≥ 1` and every zero copy satisfies
`cos (π/(k+1)) ((Im ρ)² + (Re ρ − ½)²) ≤ (Im ρ)² − (Re ρ − ½)²`, then `ξ(½ + x)` has the `PF_k`
Taylor property. -/
theorem pfTaylorAtZero_XiC_neg_I_mul_of_cone {k : ℕ} (hk : 1 ≤ k)
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) :
    PFTaylorAtZero k (fun x => XiC (-(I * x))) := by
  classical
  set φ : ℂ → ℂ := fun x => -(I * x) with hφ
  have hcφ : Continuous φ := by rw [hφ]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φ (Set.mapsTo_univ φ Set.univ) hcφ.continuousOn
  set σ := xiZeroCopyReflectEquiv with hσdef
  set τ := xiZeroCopyConjEquiv with hτdef
  have hσσ : ∀ q, σ (σ q) = q := xiZeroCopyReflectEquiv_apply_apply
  have hττ : ∀ q, τ (τ q) = q := xiZeroCopyConjEquiv_apply_apply
  have hστ : ∀ q, σ (τ q) = τ (σ q) := xiZeroCopyReflectEquiv_conjEquiv_comm
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S =>
    S ∪ S.image σ ∪ S.image τ ∪ S.image (fun q => σ (τ q))
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => by
      intro q hq
      simp only [c, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl hq))) tendsto_id
  have hclσ : ∀ S, ∀ a ∈ c S, σ a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ((ha | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩
    · exact Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩))
    · exact Or.inl (Or.inl (Or.inl (by rw [hσσ]; exact hb)))
    · exact Or.inr ⟨b, hb, rfl⟩
    · exact Or.inl (Or.inr ⟨b, hb, by rw [hσσ]⟩)
  have hclτ : ∀ S, ∀ a ∈ c S, τ a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ((ha | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩
    · exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
    · exact Or.inr ⟨b, hb, by rw [hστ]⟩
    · exact Or.inl (Or.inl (Or.inl (by rw [hττ]; exact hb)))
    · exact Or.inl (Or.inl (Or.inr ⟨b, hb, by rw [← hστ, hττ]⟩))
  have hm' := tendstoLocallyUniformlyOn_comp_index hm hc
  set f : XiZeroCopy → ℂ → ℂ := fun q x => weierstrassE1 (φ x / xiSpectralPoint q) with hf
  have hsmall : ∀ q, (τ q = q ∨ τ q = σ q) → PFTaylorAtZero k (f q * f (σ q)) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := xiZeroCopyConjEquiv_ne_of_re_ne hne
      rcases hq with h | h
      · exact h1 h
      · exact h2 h
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]
      simp
    have hγ : (q.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hz, h0, Complex.ofReal_zero]
    set γ := (q.1 : ℂ).im
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    have e : f q * f (σ q) = fun x : ℂ => ((1 : ℝ) : ℂ) + ((1 / γ ^ 2 : ℝ) : ℂ) * x ^ 2 +
        ((0 : ℝ) : ℂ) * x ^ 4 := by
      funext x
      simp only [Pi.mul_apply, hf, hφ, hσdef, xiSpectralPoint_reflect, hz]
      rw [weierstrassE1_centre_pair hγc x]
      push_cast
      field_simp
      ring
    rw [e]
    exact pfTaylorAtZero_linear k zero_le_one (by positivity)
  have hbig : ∀ q, τ q ≠ q → τ q ≠ σ q →
      PFTaylorAtZero k ((f q * f (σ q)) * (f (τ q) * f (σ (τ q)))) := by
    intro q _ _
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hzτ : xiSpectralPoint (τ q) = -(starRingEnd ℂ ((a : ℂ) + cc * I)) := by
      rw [hτdef, xiSpectralPoint_conjEquiv, hz]
    have hzτ0 : -(starRingEnd ℂ ((a : ℂ) + cc * I)) ≠ 0 := by
      rw [← hzτ]; exact xiSpectralPoint_ne_zero _
    have e : (f q * f (σ q)) * (f (τ q) * f (σ (τ q))) = fun x =>
        ((1 / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * (a ^ 2 - cc ^ 2) : ℝ) : ℂ) * x ^ 2 +
            (((a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      rw [← centre_offLine_factor_eq hz0]
      funext x
      simp only [Pi.mul_apply, hf, hφ, hσdef, xiSpectralPoint_reflect]
      rw [hz, hzτ, weierstrassE1_centre_pair hz0 x, weierstrassE1_centre_pair hzτ0 x, neg_sq]
    rw [e]
    have hcone' : Real.cos (Real.pi / ((k : ℝ) + 1)) * (a ^ 2 + cc ^ 2) ≤ a ^ 2 - cc ^ 2 := by
      have h := hcone q
      have hc2 : cc ^ 2 = ((q.1 : ℂ).re - 1 / 2) ^ 2 := by rw [hcc]; ring
      rw [hc2, ha]
      exact h
    have hpos : 0 < a ^ 2 + cc ^ 2 := by
      by_contra hle
      push Not at hle
      have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg cc]
      have hc0 : cc = 0 := by nlinarith [sq_nonneg a, sq_nonneg cc]
      apply hz0
      rw [ha0, hc0]
      simp
    exact pfTaylorAtZero_quartic_of_cone hk (by positivity) (sq_nonneg _) (sq_nonneg _) hpos
      hcone'
  have hfin : ∀ S : Finset XiZeroCopy, PFTaylorAtZero k
      ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φ) := by
    intro S
    have e : ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φ) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Function.comp_apply, hf]
    rw [e]
    exact prod_of_kleinOrbits_of_mul (by simpa using pfTaylorAtZero_const k zero_le_one)
      (fun _ _ hf hg => hf.mul hg) σ τ hσσ hττ hστ xiZeroCopyReflectEquiv_ne_self f
      hsmall hbig (c S) (hclσ S) (hclτ S)
  have hlim : PFTaylorAtZero k (xiCanonicalProduct ∘ φ) :=
    PFTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      (hPdiff.comp (by rw [hφ]; fun_prop)) hm'
  have e : (fun x => XiC (-(I * x))) =
      (fun _ => (((xi ((1 / 2 : ℝ) : ℂ)).re : ℝ) : ℂ)) * (xiCanonicalProduct ∘ φ) := by
    funext x
    have hX := congrFun XiC_eq_constant_mul_canonicalProduct (-(I * x))
    simp only [Pi.mul_apply] at hX
    rw [hX, XiC_zero_eq_ofReal]
    rfl
  rw [e]
  exact (pfTaylorAtZero_const k re_xi_half_pos.le).mul hlim

/-- **`PF_k` Taylor coefficients of `ξ` at the centre inside the visibility cone.** -/
theorem xi_centre_pfSeq_of_cone {k : ℕ} (hk : 1 ≤ k)
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) :
    PFSeq k (evenTaylorRe (fun x => xi (1 / 2 + x))) := by
  have e : (fun x => xi (1 / 2 + x)) = fun x => XiC (-(I * x)) := by
    funext x
    simp only [XiC]
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e]
  exact (pfTaylorAtZero_XiC_neg_I_mul_of_cone hk hcone).2.2

/-! ## Order thirty-seven at the centre, unconditionally -/

/-- `1 − cos (π/38) ≥ 3411/10⁶`, from `cos x ≤ 1 − x²/2 + 5x⁴/96` and `3.14 < π < 3.15`. -/
theorem one_sub_cos_pi_div_thirtyEight_ge : (3411 / 1000000 : ℝ) ≤ 1 - Real.cos (Real.pi / 38) := by
  have hπlo := Real.pi_gt_d2
  have hπhi := Real.pi_lt_d2
  set θ := Real.pi / 38 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθlo : 3.14 / 38 < θ := by
    rw [hθ]
    exact div_lt_div_of_pos_right hπlo (by norm_num)
  have hθhi : θ < 3.15 / 38 := by
    rw [hθ]
    exact div_lt_div_of_pos_right hπhi (by norm_num)
  have hθ1 : |θ| ≤ 1 := by
    rw [abs_of_nonneg hθ0]
    linarith
  have hb := Real.cos_bound hθ1
  rw [abs_of_nonneg hθ0] at hb
  have hb2 := (abs_le.mp hb).2
  have h2 : (3.14 / 38 : ℝ) ^ 2 < θ ^ 2 := pow_lt_pow_left₀ hθlo (by norm_num) (by norm_num)
  have h4 : θ ^ 4 < (3.15 / 38 : ℝ) ^ 4 := pow_lt_pow_left₀ hθhi hθ0 (by norm_num)
  norm_num at h2 h4
  linarith

/-- Every zero copy lies in the order-`37` visibility cone at the centre: critical zeros trivially,
off-line zeros because `Im² ≥ 2365/16` and `(Re − ½)² < ¼`. -/
theorem pf37Cone_centre (q : XiZeroCopy) :
    Real.cos (Real.pi / (((37 : ℕ) : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  rw [show (((37 : ℕ) : ℝ) + 1) = 38 by norm_num]
  have hcos1 := Real.cos_le_one (Real.pi / 38)
  have hL := one_sub_cos_pi_div_thirtyEight_ge
  by_cases hh : (q.1 : ℂ).im ^ 2 < 2365 / 16
  · rw [xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hh, sub_self]
    have := sq_nonneg ((q.1 : ℂ).im)
    nlinarith
  · push Not at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have hc2 : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
      nlinarith [hstrip.1, hstrip.2]
    have h1 : (2365 / 16 : ℝ) * (3411 / 1000000) ≤
        (q.1 : ℂ).im ^ 2 * (1 - Real.cos (Real.pi / 38)) :=
      mul_le_mul hh hL (by norm_num) (by positivity)
    have h2 : ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 + Real.cos (Real.pi / 38)) ≤
        ((q.1 : ℂ).re - 1 / 2) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    nlinarith

/-- **The Taylor coefficients of `ξ` at the centre form a `PF_37` sequence, unconditionally.**
With `ξ(½ + x) = Σ_n a_n x^{2n}`, every Toeplitz minor `det (a_{j_c − i_r})` of order at most `37`
with increasing rows `i` and columns `j` is nonnegative. -/
theorem xi_centre_pfSeq_thirtySeven : PFSeq 37 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_cone (by norm_num) pf37Cone_centre

end

end RHTower
