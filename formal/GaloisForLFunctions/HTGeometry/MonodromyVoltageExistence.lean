import GaloisForLFunctions.HTGeometry.MonodromyVoltageLift

/-!
# Existence of a connected voltage on a hyperbolic monodromy cover

The `ZMod p`-voltages whose cyclic sums vanish form the kernel of a linear map whose rank is at
most the total number of marked-fibre points `f_a + f_b + f_c`, because each component takes
values in the space of functions invariant under the corresponding monodromy.  The coboundaries
form the image of a map with a nonzero kernel (the constants), so their span has dimension at
most `D − 1`.

Hence as soon as

```text
f_a + f_b + f_c < D,     i.e.     the covering surface has negative Euler characteristic,
```

there is a voltage which satisfies the cyclic-sum conditions and is not a coboundary — a
connected `p`-fold lift.  This is the linear-algebra form of the statement that the fundamental
group of a hyperbolic surface has nontrivial mod-`p` homology.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Finset

section Existence

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S] {p : ℕ} [Fact p.Prime]

/-- Cyclic summation along a permutation, as a linear map on voltages. -/
def cyclicSumL (σ : Perm S) (n : ℕ) : (S → ZMod p) →ₗ[ZMod p] (S → ZMod p) where
  toFun := cyclicSum σ n
  map_add' α β := by
    funext s
    simp only [cyclicSum, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r α := by
    funext s
    simp only [cyclicSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

omit [Fintype S] [DecidableEq S] in
@[simp] theorem cyclicSumL_apply (σ : Perm S) (n : ℕ) (α : S → ZMod p) :
    cyclicSumL σ n α = cyclicSum σ n α := rfl

/-- The space of functions invariant under a permutation. -/
def invariantSubmodule (σ : Perm S) : Submodule (ZMod p) (S → ZMod p) where
  carrier := {v | ∀ s, v (σ s) = v s}
  add_mem' hv hw := fun s => by simp only [Pi.add_apply, hv s, hw s]
  zero_mem' := fun s => rfl
  smul_mem' r v hv := fun s => by simp only [Pi.smul_apply, hv s]

omit [Fintype S] [DecidableEq S] in
theorem mem_invariantSubmodule_pow {σ : Perm S} {v : S → ZMod p}
    (hv : v ∈ invariantSubmodule σ) (k : ℕ) (s : S) : v ((σ ^ k) s) = v s := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : (σ ^ (k + 1)) s = σ ((σ ^ k) s) := by rw [pow_succ']; rfl
      rw [hstep, hv ((σ ^ k) s), ih]

omit [Fintype S] [DecidableEq S] in
/-- Cyclic sums are invariant functions. -/
theorem cyclicSum_mem_invariantSubmodule {σ : Perm S} {n : ℕ} (hσ : σ ^ n = 1)
    (α : S → ZMod p) : cyclicSum σ n α ∈ invariantSubmodule σ := by
  intro s
  set g : ℕ → ZMod p := fun k => α ((σ ^ k) s) with hg
  have hshift : cyclicSum σ n α (σ s) = ∑ k ∈ Finset.range n, g (k + 1) := by
    simp only [cyclicSum, hg]
    refine Finset.sum_congr rfl ?_
    intro k _
    congr 1
  have h1 : ∑ k ∈ Finset.range n, g (k + 1) + g 0 = ∑ i ∈ Finset.range (n + 1), g i :=
    (Finset.sum_range_succ' g n).symm
  have h2 : ∑ i ∈ Finset.range (n + 1), g i = ∑ i ∈ Finset.range n, g i + g n :=
    Finset.sum_range_succ g n
  have h3 : g n = g 0 := by
    simp only [hg]
    rw [hσ]
    simp
  have h4 : ∑ k ∈ Finset.range n, g (k + 1) = ∑ i ∈ Finset.range n, g i := by
    have := h1.trans h2
    rw [h3] at this
    exact add_right_cancel this
  rw [hshift, h4]
  rfl

omit [DecidableEq S] in
/-- An invariant function is determined by its values on a transversal. -/
theorem finrank_invariantSubmodule_le {σ : Perm S} {n : ℕ} {T : Finset S}
    (hT : ∀ s : S, ∃ t ∈ T, ∃ k, k < n ∧ (σ ^ k) t = s) :
    Module.finrank (ZMod p) (invariantSubmodule (p := p) σ) ≤ T.card := by
  have hle : Module.finrank (ZMod p) (invariantSubmodule (p := p) σ)
      ≤ Module.finrank (ZMod p) (↥T → ZMod p) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.funLeft (ZMod p) (ZMod p) (Subtype.val : ↥T → S)).comp
        (invariantSubmodule (p := p) σ).subtype) ?_
    intro v w hvw
    have hval : ∀ t : ↥T, (v : S → ZMod p) (t : S) = (w : S → ZMod p) (t : S) := by
      intro t
      exact congrFun hvw t
    ext s
    obtain ⟨t, htT, k, _, hkt⟩ := hT s
    have hv := mem_invariantSubmodule_pow v.2 k t
    have hw := mem_invariantSubmodule_pow w.2 k t
    rw [hkt] at hv hw
    rw [hv, hw]
    exact hval ⟨t, htT⟩
  simpa using hle

end Existence

section Construct

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S] {p : ℕ} [Fact p.Prime]
variable (F : MonodromyCover a b c S)

/-- The voltage-to-`X·Y`-voltage map. -/
def gammaMap : ((S → ZMod p) × (S → ZMod p)) →ₗ[ZMod p] (S → ZMod p) where
  toFun w := fun s => w.2 s + w.1 (F.Y s)
  map_add' w w' := by funext s; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
  map_smul' r w := by
    funext s
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The three cyclic-sum constraints, as linear maps on pairs of voltages. -/
def constraintX : ((S → ZMod p) × (S → ZMod p)) →ₗ[ZMod p] (S → ZMod p) :=
  (cyclicSumL F.X a).comp (LinearMap.fst (ZMod p) _ _)

/-- The second cyclic-sum constraint. -/
def constraintY : ((S → ZMod p) × (S → ZMod p)) →ₗ[ZMod p] (S → ZMod p) :=
  (cyclicSumL F.Y b).comp (LinearMap.snd (ZMod p) _ _)

/-- The third cyclic-sum constraint. -/
def constraintZ : ((S → ZMod p) × (S → ZMod p)) →ₗ[ZMod p] (S → ZMod p) :=
  (cyclicSumL (F.X * F.Y) c).comp (gammaMap F)

/-- The coboundary map. -/
def coboundaryMap : (S → ZMod p) →ₗ[ZMod p] ((S → ZMod p) × (S → ZMod p)) where
  toFun lam := (fun s => lam (F.X s) - lam s, fun s => lam (F.Y s) - lam s)
  map_add' lam mu := by
    refine Prod.ext ?_ ?_ <;> funext s <;> simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add] <;>
      ring
  map_smul' r lam := by
    refine Prod.ext ?_ ?_ <;> funext s <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst, Prod.smul_snd] <;>
      ring

omit [DecidableEq S] in
theorem finrank_pair : Module.finrank (ZMod p) ((S → ZMod p) × (S → ZMod p))
    = Fintype.card S + Fintype.card S := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

/-- Each constraint has rank at most the corresponding fibre count. -/
theorem finrank_range_constraint_le {σ : Perm S} {n : ℕ} {T : Finset S} (hσ : σ ^ n = 1)
    (hT : ∀ s : S, ∃ t ∈ T, ∃ k, k < n ∧ (σ ^ k) t = s)
    (L : ((S → ZMod p) × (S → ZMod p)) →ₗ[ZMod p] (S → ZMod p))
    (hL : ∀ w, L w ∈ Set.range (cyclicSum σ n)) :
    Module.finrank (ZMod p) (LinearMap.range L) ≤ T.card := by
  have hsub : LinearMap.range L ≤ invariantSubmodule (p := p) σ := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨α, hα⟩ := hL w
    rw [← hα]
    exact cyclicSum_mem_invariantSubmodule hσ α
  exact le_trans (Submodule.finrank_mono hsub) (finrank_invariantSubmodule_le hT)

/-- **Existence of a connected voltage.**  When the covering surface is hyperbolic — the total
number of marked-fibre points is smaller than the degree — every prime `p` admits a voltage
assignment satisfying the cyclic-sum conditions which is not a coboundary. -/
theorem exists_voltageData (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyp : F.fibreX + F.fibreY + F.fibreZ < F.degree) : Nonempty (VoltageData F p) := by
  classical
  obtain ⟨TX, hTXcard, hTX⟩ := F.freeX.exists_transversal ha
  obtain ⟨TY, hTYcard, hTY⟩ := F.freeY.exists_transversal hb
  obtain ⟨TZ, hTZcard, hTZ⟩ := F.freeZ.exists_transversal hc
  have hTXeq : TX.card = F.fibreX := by
    have h1 := F.a_mul_fibreX ha
    simp only [MonodromyCover.degree] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hTXcard.symm.trans h1.symm)
  have hTYeq : TY.card = F.fibreY := by
    have h1 := F.b_mul_fibreY hb
    simp only [MonodromyCover.degree] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hTYcard.symm.trans h1.symm)
  have hTZeq : TZ.card = F.fibreZ := by
    have h1 := F.c_mul_fibreZ hc
    simp only [MonodromyCover.degree] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hTZcard.symm.trans h1.symm)
  -- ranks of the three constraints
  have hrX : Module.finrank (ZMod p) (LinearMap.range (constraintX (p := p) F)) ≤ F.fibreX := by
    rw [← hTXeq]
    exact finrank_range_constraint_le F.freeX.pow_eq_one hTX _ (fun w => ⟨w.1, rfl⟩)
  have hrY : Module.finrank (ZMod p) (LinearMap.range (constraintY (p := p) F)) ≤ F.fibreY := by
    rw [← hTYeq]
    exact finrank_range_constraint_le F.freeY.pow_eq_one hTY _ (fun w => ⟨w.2, rfl⟩)
  have hrZ : Module.finrank (ZMod p) (LinearMap.range (constraintZ (p := p) F)) ≤ F.fibreZ := by
    rw [← hTZeq]
    exact finrank_range_constraint_le F.freeZ.pow_eq_one hTZ _ (fun w => ⟨gammaMap F w, rfl⟩)
  set D := Fintype.card S with hD
  have hN : Module.finrank (ZMod p) ((S → ZMod p) × (S → ZMod p)) = D + D := finrank_pair
  have hDD : Module.finrank (ZMod p) (S → ZMod p) = D :=
    Module.finrank_fintype_fun_eq_card (ZMod p)
  set W₁ := LinearMap.ker (constraintX (p := p) F) with hW₁
  set W₂ := LinearMap.ker (constraintY (p := p) F) with hW₂
  set W₃ := LinearMap.ker (constraintZ (p := p) F) with hW₃
  have hrkX : Module.finrank (ZMod p) (LinearMap.range (constraintX (p := p) F))
      + Module.finrank (ZMod p) W₁ = D + D := by
    rw [hW₁, ← hN]
    exact LinearMap.finrank_range_add_finrank_ker _
  have hrkY : Module.finrank (ZMod p) (LinearMap.range (constraintY (p := p) F))
      + Module.finrank (ZMod p) W₂ = D + D := by
    rw [hW₂, ← hN]
    exact LinearMap.finrank_range_add_finrank_ker _
  have hrkZ : Module.finrank (ZMod p) (LinearMap.range (constraintZ (p := p) F))
      + Module.finrank (ZMod p) W₃ = D + D := by
    rw [hW₃, ← hN]
    exact LinearMap.finrank_range_add_finrank_ker _
  -- intersections
  have hinf12 : Module.finrank (ZMod p) ↥(W₁ ⊔ W₂) + Module.finrank (ZMod p) ↥(W₁ ⊓ W₂)
      = Module.finrank (ZMod p) W₁ + Module.finrank (ZMod p) W₂ :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  have hle12 : Module.finrank (ZMod p) ↥(W₁ ⊔ W₂) ≤ D + D := by
    rw [← hN]; exact Submodule.finrank_le _
  have hinf123 : Module.finrank (ZMod p) ↥((W₁ ⊓ W₂) ⊔ W₃)
      + Module.finrank (ZMod p) ↥((W₁ ⊓ W₂) ⊓ W₃)
      = Module.finrank (ZMod p) ↥(W₁ ⊓ W₂) + Module.finrank (ZMod p) W₃ :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  have hle123 : Module.finrank (ZMod p) ↥((W₁ ⊓ W₂) ⊔ W₃) ≤ D + D := by
    rw [← hN]; exact Submodule.finrank_le _
  -- the coboundary image
  have hDpos : 0 < D := by
    simp only [MonodromyCover.degree] at hhyp
    omega
  have hSne : Nonempty S := by
    rw [← Fintype.card_pos_iff]
    exact hDpos
  have hone : (1 : S → ZMod p) ≠ 0 := by
    intro hcon
    obtain ⟨s⟩ := hSne
    have := congrFun hcon s
    simp at this
  have hspan : Submodule.span (ZMod p) {(1 : S → ZMod p)} ≤ LinearMap.ker (coboundaryMap F) := by
    rw [Submodule.span_le]
    rintro _ rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    refine Prod.ext ?_ ?_ <;> funext s <;> simp [coboundaryMap]
  have hkerpos : 1 ≤ Module.finrank (ZMod p) (LinearMap.ker (coboundaryMap (p := p) F)) := by
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {(1 : S → ZMod p)}) = 1 :=
      finrank_span_singleton hone
    rw [← h1]
    exact Submodule.finrank_mono hspan
  have hcob : Module.finrank (ZMod p) (LinearMap.range (coboundaryMap (p := p) F))
      + Module.finrank (ZMod p) (LinearMap.ker (coboundaryMap (p := p) F)) = D := by
    rw [← hDD]
    exact LinearMap.finrank_range_add_finrank_ker _
  -- dimension count
  have hbig : Module.finrank (ZMod p) (LinearMap.range (coboundaryMap (p := p) F))
      < Module.finrank (ZMod p) ↥((W₁ ⊓ W₂) ⊓ W₃) := by
    simp only [MonodromyCover.degree] at hhyp
    omega
  have hnotle : ¬ ((W₁ ⊓ W₂) ⊓ W₃ ≤ LinearMap.range (coboundaryMap (p := p) F)) := by
    intro hle
    exact absurd (Submodule.finrank_mono hle) (not_le.mpr hbig)
  obtain ⟨w, hwW, hwnot⟩ := SetLike.not_le_iff_exists.mp hnotle
  refine ⟨{ alpha := w.1, beta := w.2, sumX := ?_, sumY := ?_, sumZ := ?_, notCoboundary := ?_ }⟩
  · intro s
    have : constraintX (p := p) F w = 0 := hwW.1.1
    exact congrFun this s
  · intro s
    have : constraintY (p := p) F w = 0 := hwW.1.2
    exact congrFun this s
  · intro s
    have : constraintZ (p := p) F w = 0 := hwW.2
    exact congrFun this s
  · rintro ⟨lam, hlam1, hlam2⟩
    refine hwnot ⟨lam, ?_⟩
    refine Prod.ext ?_ ?_
    · funext s; exact (hlam1 s).symm
    · funext s; exact (hlam2 s).symm

end Construct

end GaloisForLFunctions.HTGeometry
