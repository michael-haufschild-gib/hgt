import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpVectorArtinian
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpSemilinearAut

/-!
# Forward hulls of a lattice and their divisible parts

For a uniformizer-semilinear automorphism `T` and a lattice `Λ`, the forward hull
`Λ_∞ = Λ + TΛ + T²Λ + ⋯` is an integral submodule stable under `T`.  It need not be a lattice: its
**divisible part** `⋂_k ϖ^k Λ_∞`, the largest subspace it contains, measures how far it is from one.

* `DiffOp.divisiblePart` — the divisible part of an integral submodule, a skew subspace.
* `DiffOp.exists_le_divisiblePart_sup_uniformizerDilate` — **the divisible-part lemma**: an integral
  submodule `M` between a lattice `Λ` and its span is bounded modulo its divisible part,
  `M ⊆ W' + ϖ^{-c} Λ`.  The chain `ϖ^k M + Λ` stabilizes at some `Y` (Artinian quotient), and then
  `Y = ϖY + Λ`; unwinding this identity writes each `y ∈ Y` as a convergent series `Σ ϖ^j λ_j` plus
  an element of every `ϖ^k Y`, i.e. of the divisible part.
* `DiffOp.forwardHull` — the partial hulls `Λ_{n+1} = Λ + T Λ_n`, finitely generated and increasing.
* `DiffOp.exists_contracting_of_le_divisiblePart` — **exhaustion**: if the divisible part of the hull
  is the whole span `W` of `Λ` (and `W` is `T⁻¹`-stable), then `T⁻¹Λ` lies in some `Λ_{n₂}`, after
  which `Λ_{n+1} = TΛ_n`; the lattice `P = Λ_{n₂}` then satisfies `ϖ^{-1} P ⊆ T^m P` for one `m ≥ 1`,
  i.e. `T⁻¹` contracts `P` uniformly.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

/-- The divisible part `⋂_k ϖ^k M` of an integral submodule, a skew subspace. -/
def divisiblePart (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    Submodule (CompletedPseudoDiffOp K) E where
  carrier := {x | ∀ k : ℕ, x ∈ uniformizerDilate (k : ℤ) M}
  add_mem' hx hy k := Submodule.add_mem _ (hx k) (hy k)
  zero_mem' k := Submodule.zero_mem _
  smul_mem' a x hx k := by
    obtain ⟨t, ht⟩ := exists_uniformizer_left_scale_mem_integer a
    have hox : (⟨uniformizerZPow (K := K) t * a, ht⟩ : CompletedPseudoDiffOpInteger (K := K)) • x ∈
        uniformizerDilate (((k : ℤ) + t).toNat : ℤ) M :=
      Submodule.smul_mem _ _ (hx _)
    have hscaled := smul_mem_uniformizerDilate (-t) hox
    rw [uniformizerDilate_uniformizerDilate, integer_smul_eq, smul_smul] at hscaled
    change (uniformizerZPow (K := K) (-t) * (uniformizerZPow (K := K) t * a)) • x ∈ _ at hscaled
    rw [← mul_assoc, uniformizerZPow_neg_mul, one_mul] at hscaled
    exact uniformizerDilate_antitone M (by omega) hscaled

variable {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

theorem mem_divisiblePart {x : E} :
    x ∈ divisiblePart M ↔ ∀ k : ℕ, x ∈ uniformizerDilate (k : ℤ) M := Iff.rfl

theorem divisiblePart_le :
    (divisiblePart M).restrictScalars (CompletedPseudoDiffOpInteger (K := K)) ≤ M := by
  intro x hx
  have := hx 0
  rwa [Nat.cast_zero, uniformizerDilate_zero] at this

/-- Every subspace inside an integral submodule lies in its divisible part. -/
theorem le_divisiblePart {V : Submodule (CompletedPseudoDiffOp K) E}
    (hV : V.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) ≤ M) :
    V ≤ divisiblePart M := by
  intro x hx k
  have := uniformizerDilate_mono (k := (k : ℤ)) hV
  rw [uniformizerDilate_restrictScalars] at this
  exact this hx

/-- A finitely generated submodule inside the union of an increasing chain lies in one member. -/
theorem exists_le_of_fg_le_iSup {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hN : N.FG) (H : ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) E) (hH : Monotone H)
    (hle : N ≤ ⨆ n, H n) : ∃ n, N ≤ H n := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hgen : ∀ x ∈ S, ∃ n, x ∈ H n := fun x hx =>
    (Submodule.mem_iSup_of_directed H hH.directed_le).1 (hle (Submodule.subset_span hx))
  choose f hf using hgen
  refine ⟨S.attach.sup (fun x => f x.1 x.2), ?_⟩
  rw [Submodule.span_le]
  intro x hx
  exact hH (Finset.le_sup (f := fun x : S => f x.1 x.2) (Finset.mem_attach S ⟨x, hx⟩)) (hf x hx)

section Hull

variable {T : (E ≃ₗ[ℤ] E)} (hT : IsUniformizerSemilinear (K := K) T)

/-- The partial forward hulls `Λ₀ = Λ`, `Λ_{n+1} = Λ + T Λ_n`. -/
def forwardHull (Λ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) E
  | 0 => Λ
  | n + 1 => Λ ⊔ semilinearImage T hT (forwardHull Λ n)

variable {Λ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

theorem forwardHull_zero : forwardHull hT Λ 0 = Λ := rfl

theorem forwardHull_succ (n : ℕ) :
    forwardHull hT Λ (n + 1) = Λ ⊔ semilinearImage T hT (forwardHull hT Λ n) := rfl

theorem le_forwardHull (n : ℕ) : Λ ≤ forwardHull hT Λ n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left

theorem semilinearImage_forwardHull_le (n : ℕ) :
    semilinearImage T hT (forwardHull hT Λ n) ≤ forwardHull hT Λ (n + 1) := le_sup_right

theorem forwardHull_mono : Monotone (forwardHull hT Λ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact le_forwardHull hT 1
  | succ n ih => exact sup_le_sup_left (semilinearImage_mono ih) _

theorem forwardHull_fg (hΛ : Λ.FG) (n : ℕ) : (forwardHull hT Λ n).FG := by
  induction n with
  | zero => exact hΛ
  | succ n ih => exact hΛ.sup (semilinearImage_fg ih)

/-- The partial hulls stay inside a `T`-stable subspace containing `Λ`. -/
theorem forwardHull_le_of_invariant {W : Submodule (CompletedPseudoDiffOp K) E}
    (hΛW : Λ ≤ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)))
    (hW : ∀ x ∈ W, T x ∈ W) (n : ℕ) :
    forwardHull hT Λ n ≤ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
  induction n with
  | zero => exact hΛW
  | succ n ih =>
      refine sup_le hΛW ?_
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
      exact hW x (ih hx)

/-- The full forward hull `Λ + TΛ + T²Λ + ⋯`. -/
def forwardHullSup (Λ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) E :=
  ⨆ n, forwardHull hT Λ n

theorem mem_forwardHullSup {x : E} : x ∈ forwardHullSup hT Λ ↔ ∃ n, x ∈ forwardHull hT Λ n :=
  Submodule.mem_iSup_of_directed _ (forwardHull_mono hT).directed_le

theorem forwardHull_le_forwardHullSup (n : ℕ) : forwardHull hT Λ n ≤ forwardHullSup hT Λ :=
  le_iSup (forwardHull hT Λ) n

theorem apply_mem_forwardHullSup {x : E} (hx : x ∈ forwardHullSup hT Λ) :
    T x ∈ forwardHullSup hT Λ := by
  obtain ⟨n, hn⟩ := (mem_forwardHullSup hT).1 hx
  exact forwardHull_le_forwardHullSup hT (n + 1)
    (semilinearImage_forwardHull_le hT n (apply_mem_semilinearImage hn))

theorem le_forwardHullSup : Λ ≤ forwardHullSup hT Λ :=
  (le_forwardHull hT 0).trans (forwardHull_le_forwardHullSup hT 0)

theorem semilinearImage_pow_zero {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (h : IsUniformizerSemilinear (K := K) (T ^ 0)) : semilinearImage (T ^ 0) h M = M := by
  ext y
  rw [mem_semilinearImage, pow_zero, inv_one]
  rfl

theorem semilinearImage_pow_succ {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (n : ℕ)
    (h : IsUniformizerSemilinear (K := K) (T ^ (n + 1)))
    (h' : IsUniformizerSemilinear (K := K) (T ^ n)) :
    semilinearImage (T ^ (n + 1)) h M = semilinearImage T hT (semilinearImage (T ^ n) h' M) := by
  ext y
  rw [mem_semilinearImage, mem_semilinearImage, mem_semilinearImage, pow_succ', mul_inv_rev,
    LinearEquiv.mul_apply]

/-- **Exhaustion.**  If the divisible part of the forward hull fills the span `W` of `Λ`, and `W` is
stable under `T` and `T⁻¹`, then `T⁻¹` contracts some lattice of `W` uniformly. -/
theorem exists_contracting_of_le_divisiblePart (hΛ : Λ.FG)
    (hfwd : ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E),
      T x ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E))
    (hinv : ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E),
      T⁻¹ x ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E))
    (hdiv : Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E) ≤
      divisiblePart (forwardHullSup hT Λ)) :
    ∃ P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, P.FG ∧ Λ ≤ P ∧
      (P : Set E) ⊆ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E) ∧
      ∃ m : ℕ, 1 ≤ m ∧ uniformizerDilate (-1) P ≤ semilinearImage (T ^ m) (hT.pow m) P := by
  classical
  have hWhull : ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E),
      x ∈ forwardHullSup hT Λ := fun x hx => divisiblePart_le (hdiv hx)
  have hΛW : Λ ≤ (Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E)).restrictScalars
      (CompletedPseudoDiffOpInteger (K := K)) := fun x hx => Submodule.subset_span hx
  obtain ⟨n₂, hn₂⟩ := exists_le_of_fg_le_iSup (semilinearImage_fg (hT := hT.inv) hΛ)
    (forwardHull hT Λ) (forwardHull_mono hT) (by
      intro y hy
      rw [mem_semilinearImage, inv_inv] at hy
      have hyW : T⁻¹ (T y) ∈ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E) :=
        hinv _ (Submodule.subset_span hy)
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at hyW
      exact hWhull y hyW)
  have hstable : ∀ n, n₂ ≤ n →
      forwardHull hT Λ (n + 1) = semilinearImage T hT (forwardHull hT Λ n) := by
    intro n hn
    refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
    intro x hx
    rw [mem_semilinearImage]
    refine forwardHull_mono hT hn (hn₂ ?_)
    rw [mem_semilinearImage, inv_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact hx
  set P := forwardHull hT Λ n₂ with hPdef
  have hpow : ∀ j : ℕ, semilinearImage (T ^ j) (hT.pow j) P = forwardHull hT Λ (n₂ + j) := by
    intro j
    induction j with
    | zero => rw [semilinearImage_pow_zero]; rfl
    | succ j ih =>
        rw [semilinearImage_pow_succ hT j _ (hT.pow j), ih, ← add_assoc,
          hstable (n₂ + j) (by omega)]
  have hPW := forwardHull_le_of_invariant hT hΛW hfwd n₂
  have hdilW : uniformizerDilate (-1) P ≤ (Submodule.span (CompletedPseudoDiffOp K)
      (Λ : Set E)).restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
    have := uniformizerDilate_mono (k := -1) hPW
    rwa [uniformizerDilate_restrictScalars] at this
  obtain ⟨n₃, hn₃⟩ := exists_le_of_fg_le_iSup (uniformizerDilate_fg (-1) (forwardHull_fg hT hΛ n₂))
    (forwardHull hT Λ) (forwardHull_mono hT) (fun x hx => hWhull x (hdilW hx))
  refine ⟨P, forwardHull_fg hT hΛ n₂, le_forwardHull hT n₂, fun x hx => hPW hx,
    n₃ - n₂ + 1, by omega, ?_⟩
  rw [hpow]
  exact hn₃.trans (forwardHull_mono hT (by omega))

end Hull

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- **Divisible-part lemma.**  An integral submodule between a lattice and its span is bounded
modulo its divisible part. -/
theorem exists_le_divisiblePart_sup_uniformizerDilate
    {Λ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hΛ : Λ.FG) (hΛM : Λ ≤ M)
    (hM : (M : Set E) ⊆ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E)) :
    ∃ c : ℕ, M ≤ (divisiblePart M).restrictScalars (CompletedPseudoDiffOpInteger (K := K)) ⊔
      uniformizerDilate (-(c : ℤ)) Λ := by
  classical
  let Y : ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) E :=
    fun k => uniformizerDilate (k : ℤ) M ⊔ Λ
  have hdilM : ∀ k : ℕ, uniformizerDilate (k : ℤ) M ≤ M := fun k => by
    have := uniformizerDilate_antitone M (show (0 : ℤ) ≤ k by positivity)
    rwa [uniformizerDilate_zero] at this
  have hYM : ∀ k, Y k ≤ M := fun k => sup_le (hdilM k) hΛM
  have hYanti : Antitone Y := fun a b hab =>
    sup_le_sup_right (uniformizerDilate_antitone M (by exact_mod_cast hab)) _
  obtain ⟨k₀, hk₀⟩ := exists_stabilizes_of_lattice_le Y hYanti (fun _ => le_sup_right)
    (fun k x hx => hM (hYM k hx))
  have hstep : ∀ y ∈ Y k₀, ∃ y' ∈ Y k₀, ∃ l ∈ Λ, y = uniformizerZPow (K := K) 1 • y' + l := by
    intro y hy
    rw [← hk₀ (k₀ + 1) (by omega)] at hy
    obtain ⟨z, hz, l, hl, rfl⟩ := Submodule.mem_sup.1 hy
    rw [show ((k₀ + 1 : ℕ) : ℤ) = 1 + (k₀ : ℤ) by push_cast; ring,
      ← uniformizerDilate_uniformizerDilate] at hz
    obtain ⟨z', hz', rfl⟩ := mem_uniformizerDilate_iff_exists.1 hz
    exact ⟨z', Submodule.mem_sup_left hz', l, hl, rfl⟩
  choose! nxt hnxt lam hlam hdecomp using hstep
  have hYdiv : Y k₀ ≤ (divisiblePart M).restrictScalars (CompletedPseudoDiffOpInteger (K := K)) ⊔ Λ := by
    intro y hy
    let ys : ℕ → E := fun n => nxt^[n] y
    have hys : ∀ n, ys n ∈ Y k₀ := by
      intro n
      induction n with
      | zero => exact hy
      | succ n ih =>
          change nxt^[n + 1] y ∈ Y k₀
          rw [Function.iterate_succ_apply']
          exact hnxt _ ih
    let s : ℕ → E := fun n => ∑ j ∈ Finset.range n, uniformizerZPow (K := K) (j : ℤ) • lam (ys j)
    have hid : ∀ n, y = s n + uniformizerZPow (K := K) (n : ℤ) • ys n := by
      intro n
      induction n with
      | zero => simp [s, ys]
      | succ n ih =>
          have hsplit := hdecomp (ys n) (hys n)
          have hnext : ys (n + 1) = nxt (ys n) := by
            change nxt^[n + 1] y = nxt (nxt^[n] y)
            rw [Function.iterate_succ_apply']
          rw [ih, hsplit, smul_add, smul_smul, ← uniformizerZPow_add, hnext]
          simp only [s, Finset.sum_range_succ]
          rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
          abel
    have hterm : ∀ j : ℕ, uniformizerZPow (K := K) (j : ℤ) • lam (ys j) ∈
        uniformizerDilate (j : ℤ) Λ := fun j => smul_mem_uniformizerDilate _ (hlam _ (hys j))
    obtain ⟨ℓ, hℓ⟩ := exists_limit_of_eventually_sub_mem_uniformizerDilate hΛ s (by
      intro k
      refine eventually_atTop.2 ⟨k, fun n hn => ?_⟩
      have : s (n + 1) - s n = uniformizerZPow (K := K) (n : ℤ) • lam (ys n) := by
        simp only [s, Finset.sum_range_succ, add_sub_cancel_left]
      rw [this]
      exact uniformizerDilate_antitone Λ (by exact_mod_cast hn) (hterm n))
    have hsΛ : ∀ n, s n ∈ Λ := by
      intro n
      refine Submodule.sum_mem _ fun j _ => ?_
      have := uniformizerDilate_antitone Λ (show (0 : ℤ) ≤ j by positivity) (hterm j)
      rwa [uniformizerDilate_zero] at this
    have hℓΛ : ℓ ∈ Λ := by
      obtain ⟨n, hn⟩ := (hℓ 0).exists
      rw [Nat.cast_zero, uniformizerDilate_zero] at hn
      have := Submodule.add_mem _ hn (hsΛ n)
      rwa [sub_add_cancel] at this
    have hdiv : y - ℓ ∈ divisiblePart M := by
      intro k
      obtain ⟨n, hn⟩ := ((hℓ k).and (eventually_ge_atTop k)).exists
      have hrepr : y - ℓ = uniformizerZPow (K := K) (n : ℤ) • ys n - (ℓ - s n) := by
        rw [hid n]
        abel
      rw [hrepr]
      refine Submodule.sub_mem _ ?_ ?_
      · have h1 := smul_mem_uniformizerDilate (n : ℤ) (hys n)
        have h2 := uniformizerDilate_mono (k := (n : ℤ)) (hYM k₀) h1
        exact uniformizerDilate_antitone M (by exact_mod_cast hn.2) h2
      · exact uniformizerDilate_mono hΛM hn.1
    have : y = (y - ℓ) + ℓ := by abel
    rw [this]
    exact Submodule.add_mem_sup hdiv hℓΛ
  refine ⟨k₀, ?_⟩
  have hMle : M ≤ uniformizerDilate (-(k₀ : ℤ)) (Y k₀) :=
    uniformizerDilate_le_iff.1 (le_sup_left : uniformizerDilate (k₀ : ℤ) M ≤ Y k₀)
  refine hMle.trans ?_
  refine (uniformizerDilate_mono hYdiv).trans ?_
  rw [uniformizerDilate_sup, uniformizerDilate_restrictScalars]


end

end DiffOp

end GaloisForLFunctions.HTGeometry
