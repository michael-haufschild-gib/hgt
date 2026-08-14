import GaloisForLFunctions.HTGeometry.OrbifoldMonodromyCover

/-!
# Cyclic voltage lifts of a monodromy cover

A `ZMod p`-*voltage assignment* on a monodromy cover `(X, Y)` of the `(a,b,c)` orbifold is a pair
of functions `α, β : S → ZMod p`.  It lifts the cover to the sheet set `S × ZMod p` by

```text
X' (s, i) = (X s, i + α s),      Y' (s, i) = (Y s, i + β s).
```

The lift is again a monodromy cover of the *same* orbifold exactly when the cyclic sums of the
voltages around every orbit of `X`, `Y` and `X · Y` vanish, and it is *connected* exactly when the
voltage is not a coboundary `α = λ ∘ X − λ`, `β = λ ∘ Y − λ`.  Its degree is `p` times the degree
of the original cover.

This is the covering-space step behind unbounded correspondence degree: it converts one cover of
the `(2,3,7)` orbifold into covers of arbitrarily large degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Finset

section Lift

variable {S : Type*} [Fintype S] [DecidableEq S] {p : ℕ}

/-- The cyclic sum of a voltage along the first `n` steps of a `σ`-orbit. -/
def cyclicSum (σ : Perm S) (n : ℕ) (α : S → ZMod p) (s : S) : ZMod p :=
  ∑ k ∈ Finset.range n, α ((σ ^ k) s)

/-- The permutation of the lifted sheet set attached to a voltage. -/
def liftPerm (σ : Perm S) (α : S → ZMod p) : Perm (S × ZMod p) where
  toFun q := (σ q.1, q.2 + α q.1)
  invFun q := (σ⁻¹ q.1, q.2 - α (σ⁻¹ q.1))
  left_inv q := by simp
  right_inv q := by simp

@[simp] theorem liftPerm_apply (σ : Perm S) (α : S → ZMod p) (q : S × ZMod p) :
    liftPerm σ α q = (σ q.1, q.2 + α q.1) := rfl

theorem liftPerm_pow (σ : Perm S) (α : S → ZMod p) (n : ℕ) (q : S × ZMod p) :
    ((liftPerm σ α) ^ n) q = ((σ ^ n) q.1, q.2 + cyclicSum σ n α q.1) := by
  induction n with
  | zero => simp [cyclicSum]
  | succ n ih =>
      rw [pow_succ']
      simp only [Equiv.Perm.mul_apply, ih, liftPerm_apply]
      have h1 : σ ((σ ^ n) q.1) = (σ ^ (n + 1)) q.1 := by rw [pow_succ']; rfl
      have h2 : q.2 + cyclicSum σ n α q.1 + α ((σ ^ n) q.1)
          = q.2 + cyclicSum σ (n + 1) α q.1 := by
        simp only [cyclicSum, Finset.sum_range_succ]
        ring
      rw [h1, h2]

theorem liftPerm_mul (σ τ : Perm S) (α β : S → ZMod p) :
    liftPerm σ α * liftPerm τ β = liftPerm (σ * τ) (fun s => β s + α (τ s)) := by
  ext q
  · rfl
  · simp only [Equiv.Perm.mul_apply, liftPerm_apply]
    ring

/-- Freeness is inherited by the lift: the base coordinate already moves. -/
theorem isFreeOfOrder_liftPerm {σ : Perm S} {α : S → ZMod p} {n : ℕ}
    (h : IsFreeOfOrder σ n) (hsum : ∀ s, cyclicSum σ n α s = 0) :
    IsFreeOfOrder (liftPerm σ α) n where
  pow_eq_one := by
    ext q
    · simp only [liftPerm_pow, Equiv.Perm.one_apply]
      rw [h.pow_eq_one]
      rfl
    · simp only [liftPerm_pow, Equiv.Perm.one_apply, hsum]
      ring
  free := by
    intro k hk0 hkn q hq
    rw [liftPerm_pow] at hq
    have h1 : ((σ ^ k) q.1) = q.1 := congrArg Prod.fst hq
    exact h.free k hk0 hkn q.1 h1

end Lift

section VoltageSection

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- A connected `ZMod p`-voltage assignment on a monodromy cover: the cyclic sums vanish (so the
lift covers the same orbifold) and the voltage is not a coboundary (so the lift is connected). -/
structure VoltageData (F : MonodromyCover a b c S) (p : ℕ) where
  /-- voltage of the first monodromy generator -/
  alpha : S → ZMod p
  /-- voltage of the second monodromy generator -/
  beta : S → ZMod p
  sumX : ∀ s, cyclicSum F.X a alpha s = 0
  sumY : ∀ s, cyclicSum F.Y b beta s = 0
  sumZ : ∀ s, cyclicSum (F.X * F.Y) c (fun t => beta t + alpha (F.Y t)) s = 0
  notCoboundary : ¬ ∃ lam : S → ZMod p,
    (∀ s, alpha s = lam (F.X s) - lam s) ∧ (∀ s, beta s = lam (F.Y s) - lam s)

namespace VoltageData

variable {F : MonodromyCover a b c S} {p : ℕ} (V : VoltageData F p)

/-- The lifted monodromy of the first generator. -/
def liftX : Perm (S × ZMod p) := liftPerm F.X V.alpha

/-- The lifted monodromy of the second generator. -/
def liftY : Perm (S × ZMod p) := liftPerm F.Y V.beta

theorem liftX_mul_liftY :
    V.liftX * V.liftY = liftPerm (F.X * F.Y) (fun s => V.beta s + V.alpha (F.Y s)) :=
  liftPerm_mul _ _ _ _

/-- Translation of the fibre coordinate. -/
def transl (d : ZMod p) : Perm (S × ZMod p) where
  toFun q := (q.1, q.2 + d)
  invFun q := (q.1, q.2 - d)
  left_inv q := by simp
  right_inv q := by simp

@[simp] theorem transl_apply (d : ZMod p) (q : S × ZMod p) : transl d q = (q.1, q.2 + d) := rfl

theorem liftPerm_comm_transl (σ : Perm S) (α : S → ZMod p) (d : ZMod p) :
    Commute (liftPerm σ α) (transl d) := by
  show liftPerm σ α * transl d = transl d * liftPerm σ α
  ext q
  · rfl
  · simp only [Equiv.Perm.mul_apply, liftPerm_apply, transl_apply]
    ring

/-- The lifted monodromy group. -/
def liftClosure : Subgroup (Perm (S × ZMod p)) :=
  Subgroup.closure ({V.liftX, V.liftY} : Set (Perm (S × ZMod p)))

theorem liftX_mem : V.liftX ∈ V.liftClosure := Subgroup.subset_closure (Or.inl rfl)

theorem liftY_mem : V.liftY ∈ V.liftClosure := Subgroup.subset_closure (Or.inr rfl)

/-- Every element of the lifted monodromy group commutes with the fibre translations. -/
theorem mem_liftClosure_comm_transl (d : ZMod p) :
    ∀ g ∈ V.liftClosure, Commute g (transl d) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => Commute g (transl d)) ?_ ?_ ?_ ?_ hg
  · rintro g (rfl | hg)
    · exact liftPerm_comm_transl _ _ _
    · simp only [Set.mem_singleton_iff] at hg
      rw [hg]
      exact liftPerm_comm_transl _ _ _
  · exact Commute.one_left _
  · intro g₁ g₂ _ _ h₁ h₂
    exact h₁.mul_left h₂
  · intro g _ hgc
    exact hgc.inv_left

/-- Every base monodromy element lifts. -/
theorem exists_lift_of_mem_closure :
    ∀ h ∈ Subgroup.closure ({F.X, F.Y} : Set (Perm S)),
      ∃ g ∈ V.liftClosure, ∀ q : S × ZMod p, (g q).1 = h q.1 := by
  intro h hh
  refine Subgroup.closure_induction
    (p := fun h _ => ∃ g ∈ V.liftClosure, ∀ q : S × ZMod p, (g q).1 = h q.1) ?_ ?_ ?_ ?_ hh
  · rintro h (rfl | hh)
    · exact ⟨V.liftX, V.liftX_mem, fun q => rfl⟩
    · simp only [Set.mem_singleton_iff] at hh
      exact ⟨V.liftY, V.liftY_mem, fun q => by rw [hh]; rfl⟩
  · exact ⟨1, one_mem _, fun q => rfl⟩
  · rintro h₁ h₂ _ _ ⟨g₁, hg₁, hq₁⟩ ⟨g₂, hg₂, hq₂⟩
    refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun q => ?_⟩
    simp only [Equiv.Perm.mul_apply]
    rw [hq₁ (g₂ q), hq₂ q]
  · rintro h _ ⟨g, hg, hq⟩
    refine ⟨g⁻¹, inv_mem hg, fun q => ?_⟩
    have hqq : (g (g⁻¹ q)).1 = h ((g⁻¹ q).1) := hq (g⁻¹ q)
    have hgg : g (g⁻¹ q) = q := by simp
    rw [hgg] at hqq
    have hfin : h⁻¹ q.1 = (g⁻¹ q).1 := by rw [hqq]; simp
    exact hfin.symm

variable [NeZero p]

/-- **Holonomy group.**  The fibre translations of the base point realised by the lifted
monodromy group. -/
def holonomy (s₀ : S) : AddSubgroup (ZMod p) where
  carrier := {d | ∃ g ∈ V.liftClosure, g (s₀, 0) = (s₀, d)}
  zero_mem' := ⟨1, one_mem _, rfl⟩
  add_mem' := by
    rintro d d' ⟨g, hg, hgd⟩ ⟨g', hg', hg'd⟩
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    have hcomm : g * transl d' = transl d' * g := V.mem_liftClosure_comm_transl d' g hg
    have hstep : g ((s₀, d') : S × ZMod p) = (s₀, d + d') := by
      have h1 : ((s₀, d') : S × ZMod p) = transl d' (s₀, 0) := by simp
      rw [h1]
      have := congrArg (fun (e : Perm (S × ZMod p)) => e ((s₀, 0) : S × ZMod p)) hcomm
      simp only [Equiv.Perm.mul_apply] at this
      rw [this, hgd]
      simp
    rw [Equiv.Perm.mul_apply, hg'd, hstep]
  neg_mem' := by
    rintro d ⟨g, hg, hgd⟩
    refine ⟨g⁻¹, inv_mem hg, ?_⟩
    have hinv : g⁻¹ ((s₀, d) : S × ZMod p) = (s₀, 0) := by
      rw [← hgd]
      simp
    have hcomm : g⁻¹ * transl (-d) = transl (-d) * g⁻¹ :=
      V.mem_liftClosure_comm_transl (-d) g⁻¹ (inv_mem hg)
    have h1 : ((s₀, 0) : S × ZMod p) = transl (-d) (s₀, d) := by simp
    rw [h1]
    have := congrArg (fun (e : Perm (S × ZMod p)) => e ((s₀, d) : S × ZMod p)) hcomm
    simp only [Equiv.Perm.mul_apply] at this
    rw [this, hinv]
    simp

theorem mem_holonomy_iff {s₀ : S} {d : ZMod p} :
    d ∈ V.holonomy s₀ ↔ ∃ g ∈ V.liftClosure, g (s₀, 0) = (s₀, d) := Iff.rfl

/-- Two lifted monodromy elements sending the base point into the same fibre differ by a
holonomy element. -/
theorem holonomy_sub_mem {s₀ s : S} {i i' : ZMod p} {g g' : Perm (S × ZMod p)}
    (hg : g ∈ V.liftClosure) (hg' : g' ∈ V.liftClosure)
    (hgi : g (s₀, 0) = (s, i)) (hg'i : g' (s₀, 0) = (s, i')) : i - i' ∈ V.holonomy s₀ := by
  refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg') hg, ?_⟩
  have hinv : g'⁻¹ ((s, i') : S × ZMod p) = (s₀, 0) := by rw [← hg'i]; simp
  have hcomm : g'⁻¹ * transl (i - i') = transl (i - i') * g'⁻¹ :=
    V.mem_liftClosure_comm_transl (i - i') g'⁻¹ (inv_mem hg')
  have h1 : ((s, i) : S × ZMod p) = transl (i - i') (s, i') := by simp
  rw [Equiv.Perm.mul_apply, hgi, h1]
  have := congrArg (fun (e : Perm (S × ZMod p)) => e ((s, i') : S × ZMod p)) hcomm
  simp only [Equiv.Perm.mul_apply] at this
  rw [this, hinv]
  simp

/-- Every sheet of the base is reached by the lifted monodromy group. -/
theorem exists_lift_over (s₀ s : S) : ∃ i : ZMod p, ∃ g ∈ V.liftClosure, g (s₀, 0) = (s, i) := by
  obtain ⟨h, hh, hhs⟩ := F.transitive s₀ s
  obtain ⟨g, hg, hgq⟩ := V.exists_lift_of_mem_closure h hh
  refine ⟨(g ((s₀, 0) : S × ZMod p)).2, g, hg, ?_⟩
  have h1 : (g ((s₀, 0) : S × ZMod p)).1 = s := by rw [hgq]; exact hhs
  exact Prod.ext h1 rfl

/-- **Triviality of the holonomy detects a coboundary.** -/
theorem exists_coboundary_of_holonomy_eq_bot (s₀ : S) (hbot : V.holonomy s₀ = ⊥) :
    ∃ lam : S → ZMod p,
      (∀ s, V.alpha s = lam (F.X s) - lam s) ∧ (∀ s, V.beta s = lam (F.Y s) - lam s) := by
  have huniq : ∀ {s : S} {i i' : ZMod p} {g g' : Perm (S × ZMod p)}, g ∈ V.liftClosure →
      g' ∈ V.liftClosure → g (s₀, 0) = (s, i) → g' (s₀, 0) = (s, i') → i = i' := by
    intro s i i' g g' hg hg' hgi hg'i
    have hmem := V.holonomy_sub_mem hg hg' hgi hg'i
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  choose lam gg hgg hggeq using V.exists_lift_over s₀
  refine ⟨lam, ?_, ?_⟩
  · intro s
    have hstep : (V.liftX * gg s) ((s₀, 0) : S × ZMod p) = (F.X s, lam s + V.alpha s) := by
      rw [Equiv.Perm.mul_apply, hggeq s]
      rfl
    have := huniq (mul_mem V.liftX_mem (hgg s)) (hgg (F.X s)) hstep (hggeq (F.X s))
    rw [← this]
    ring
  · intro s
    have hstep : (V.liftY * gg s) ((s₀, 0) : S × ZMod p) = (F.Y s, lam s + V.beta s) := by
      rw [Equiv.Perm.mul_apply, hggeq s]
      rfl
    have := huniq (mul_mem V.liftY_mem (hgg s)) (hgg (F.Y s)) hstep (hggeq (F.Y s))
    rw [← this]
    ring

/-- A nonzero holonomy element generates all of `ZMod p` when `p` is prime. -/
theorem holonomy_eq_top_of_ne_bot (hp : p.Prime) (s₀ : S) (hne : V.holonomy s₀ ≠ ⊥) :
    ∀ e : ZMod p, e ∈ V.holonomy s₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ V.holonomy s₀, d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (by
      ext x
      simp only [AddSubgroup.mem_bot]
      exact ⟨fun hx => hcon x hx, fun hx => by rw [hx]; exact (V.holonomy s₀).zero_mem⟩)
  intro e
  have hdinv : (e * d⁻¹) * d = e := by
    field_simp
  have hsm : ((e * d⁻¹).val) • d = e := by
    rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    exact hdinv
  rw [← hsm]
  exact AddSubgroup.nsmul_mem _ hd _

/-- **Connectedness of the lift.**  A non-coboundary voltage over a prime cyclic group produces a
connected cover. -/
theorem liftClosure_transitive (hp : p.Prime) (q q' : S × ZMod p) :
    ∃ g ∈ V.liftClosure, g q = q' := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact (IsEmpty.false q.1).elim
  obtain ⟨s₀⟩ := hS
  have hne : V.holonomy s₀ ≠ ⊥ := by
    intro hbot
    exact V.notCoboundary (V.exists_coboundary_of_holonomy_eq_bot s₀ hbot)
  have htop := V.holonomy_eq_top_of_ne_bot hp s₀ hne
  -- every point is reached from the base point
  have hreach : ∀ r : S × ZMod p, ∃ g ∈ V.liftClosure, g (s₀, 0) = r := by
    rintro ⟨t, j⟩
    obtain ⟨m, g, hg, hgm⟩ := V.exists_lift_over s₀ t
    obtain ⟨g', hg', hg'd⟩ := htop (j - m)
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    have hcomm : g * transl (j - m) = transl (j - m) * g :=
      V.mem_liftClosure_comm_transl (j - m) g hg
    have hstep : g ((s₀, j - m) : S × ZMod p) = (t, m + (j - m)) := by
      have h1 : ((s₀, j - m) : S × ZMod p) = transl (j - m) (s₀, 0) := by simp
      rw [h1]
      have := congrArg (fun (e : Perm (S × ZMod p)) => e ((s₀, 0) : S × ZMod p)) hcomm
      simp only [Equiv.Perm.mul_apply] at this
      rw [this, hgm]
      simp
    rw [Equiv.Perm.mul_apply, hg'd, hstep]
    simp
  obtain ⟨g₁, hg₁, hq₁⟩ := hreach q
  obtain ⟨g₂, hg₂, hq₂⟩ := hreach q'
  refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hq₁]
  simp [hq₂]

/-- **The lifted cover.**  A connected voltage assignment lifts a monodromy cover of the
`(a,b,c)` orbifold to a monodromy cover of the same orbifold, of `p` times the degree. -/
def liftCover (hp : p.Prime) : MonodromyCover a b c (S × ZMod p) where
  X := V.liftX
  Y := V.liftY
  freeX := isFreeOfOrder_liftPerm F.freeX V.sumX
  freeY := isFreeOfOrder_liftPerm F.freeY V.sumY
  freeZ := by
    rw [show V.liftX * V.liftY
      = liftPerm (F.X * F.Y) (fun s => V.beta s + V.alpha (F.Y s)) from V.liftX_mul_liftY]
    exact isFreeOfOrder_liftPerm F.freeZ V.sumZ
  transitive := V.liftClosure_transitive hp

theorem liftCover_degree (hp : p.Prime) : (V.liftCover hp).degree = F.degree * p := by
  simp [MonodromyCover.degree, liftCover, Fintype.card_prod, ZMod.card]

end VoltageData

end VoltageSection

end GaloisForLFunctions.HTGeometry
