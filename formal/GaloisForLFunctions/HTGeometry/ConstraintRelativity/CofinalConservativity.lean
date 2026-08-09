import Mathlib

/-!
# The cofinal-observer conservativity law

A finite-resource observer of a filtered object is the quotient `Q_N X = X / F^{N+1} X`.  For a
complete separated filtration, any **cofinal** family of such observers is jointly conservative: a
filtration-compatible map whose quotients are all bijective is itself bijective.

Conversely no **bounded** family of observers is jointly conservative.  On the product
`X = ∏_{n≥0} k e_n` with `F^N X = ∏_{n≥N} k e_n`, the prolongation `∇ e_n = e_{n+1}` and the
involution `τ e_n = (-1)^n e_n` satisfy `τ ∇ = −∇ τ`, and the tail `K = F^{M+1} X` is nonzero,
complete, `∇`-stable and `τ`-stable while every observer of index at most `M` sees `K` as zero.
Its zero endomorphism is therefore inverted by every such observer without being invertible.

Hence a nonstabilizing resource tower requires a countably cofinal observer atlas; no finite atlas
suffices.
-/

namespace HTGeometry.ConstraintRelativity

open Submodule

/-! ## Complete separated linear filtrations -/

/-- A decreasing, separated, complete filtration of a module by submodules. -/
structure LinearFiltration (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] where
  /-- The filtration submodules `F^n`. -/
  fil : ℕ → Submodule R M
  /-- The filtration is decreasing. -/
  antitone : Antitone fil
  /-- The filtration is separated. -/
  separated : ⨅ n, fil n = ⊥
  /-- Every Cauchy sequence converges. -/
  complete : ∀ x : ℕ → M, (∀ n, x (n + 1) - x n ∈ fil n) → ∃ L, ∀ n, L - x n ∈ fil n

namespace LinearFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (F : LinearFiltration R M)

/-- A vector lying in every filtration stage is zero. -/
theorem eq_zero_of_mem_all {x : M} (hx : ∀ n, x ∈ F.fil n) : x = 0 := by
  have hmem : x ∈ ⨅ n, F.fil n := (Submodule.mem_iInf _).2 hx
  rw [F.separated] at hmem
  simpa using hmem

end LinearFiltration

/-! ## Sufficiency: a cofinal observer family is jointly conservative -/

section Sufficiency

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An increasing selector inside a cofinal set of resource levels. -/
noncomputable def cofinalSelector (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n) : ℕ → ℕ
  | 0 => (hA 0).choose
  | k + 1 => (hA (cofinalSelector A hA k + 1)).choose

theorem cofinalSelector_mem (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n) (k : ℕ) :
    cofinalSelector A hA k ∈ A := by
  cases k with
  | zero => exact (hA 0).choose_spec.1
  | succ k => exact (hA (cofinalSelector A hA k + 1)).choose_spec.1

theorem cofinalSelector_lt (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n) (k : ℕ) :
    cofinalSelector A hA k < cofinalSelector A hA (k + 1) :=
  (hA (cofinalSelector A hA k + 1)).choose_spec.2

theorem cofinalSelector_strictMono (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n) :
    StrictMono (cofinalSelector A hA) :=
  strictMono_nat_of_lt_succ (cofinalSelector_lt A hA)

theorem le_cofinalSelector (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n) (k : ℕ) :
    k ≤ cofinalSelector A hA k :=
  (cofinalSelector_strictMono A hA).le_apply

/-- **Sufficiency, injectivity.**  If the observers at a cofinal set of resource levels are all
injective, a filtration-compatible map is injective. -/
theorem injective_of_cofinal_quotient_injective (FM : LinearFiltration R M)
    (f : M →ₗ[R] N) (FN : LinearFiltration R N) (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n)
    (hinj : ∀ n ∈ A, ∀ x : M, f x ∈ FN.fil n → x ∈ FM.fil n) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine FM.eq_zero_of_mem_all fun m => ?_
  obtain ⟨n, hnA, hmn⟩ := hA m
  exact FM.antitone hmn (hinj n hnA x (by rw [hx]; exact Submodule.zero_mem _))

/-- **Sufficiency, surjectivity.**  If the observers at a cofinal set of resource levels are all
bijective, a filtration-compatible map is surjective.  The inverse is assembled as the limit of the
level-wise inverses, which converges by completeness of the source. -/
theorem surjective_of_cofinal_quotient_bijective (FM : LinearFiltration R M)
    (f : M →ₗ[R] N) (FN : LinearFiltration R N) (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n)
    (hmap : ∀ n, Submodule.map f (FM.fil n) ≤ FN.fil n)
    (hinj : ∀ n ∈ A, ∀ x : M, f x ∈ FN.fil n → x ∈ FM.fil n)
    (hsurj : ∀ n ∈ A, ∀ y : N, ∃ x : M, y - f x ∈ FN.fil n) :
    Function.Surjective f := by
  classical
  intro y
  set s := cofinalSelector A hA with hs
  have hsA : ∀ k, s k ∈ A := cofinalSelector_mem A hA
  have hsmono : StrictMono s := cofinalSelector_strictMono A hA
  have hstep : ∀ (k : ℕ) (x : M), y - f x ∈ FN.fil (s k) →
      ∃ x' : M, y - f x' ∈ FN.fil (s (k + 1)) ∧ x' - x ∈ FM.fil (s k) := by
    intro k x hx
    obtain ⟨d, hd⟩ := hsurj (s (k + 1)) (hsA (k + 1)) (y - f x)
    refine ⟨x + d, ?_, ?_⟩
    · have hrw : y - f (x + d) = y - f x - f d := by rw [map_add]; abel
      rw [hrw]
      exact hd
    · have hfd : f d ∈ FN.fil (s k) := by
        have h1 : y - f x - (y - f x - f d) = f d := by abel
        rw [← h1]
        exact Submodule.sub_mem _ hx (FN.antitone (hsmono.monotone (Nat.le_succ k)) hd)
      have hdmem := hinj (s k) (hsA k) d hfd
      simpa using hdmem
  obtain ⟨x0, hx0⟩ := hsurj (s 0) (hsA 0) y
  choose! next hnext1 hnext2 using hstep
  let x : ℕ → M := fun k => Nat.rec x0 (fun j xj => next j xj) k
  have hxy : ∀ k, y - f (x k) ∈ FN.fil (s k) := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih => exact hnext1 k (x k) ih
  have hxstep : ∀ k, x (k + 1) - x k ∈ FM.fil (s k) := fun k => hnext2 k (x k) (hxy k)
  have hcauchy : ∀ k, x (k + 1) - x k ∈ FM.fil k := fun k =>
    FM.antitone (le_cofinalSelector A hA k) (hxstep k)
  obtain ⟨L, hL⟩ := FM.complete x hcauchy
  have htail : ∀ k j, k ≤ j → x j - x k ∈ FM.fil (s k) := by
    intro k j hkj
    induction j with
    | zero =>
        have hk : k = 0 := Nat.le_zero.1 hkj
        subst hk
        simp
    | succ j ih =>
        rcases Nat.lt_or_ge k (j + 1) with hlt | hge
        · have hkj' : k ≤ j := Nat.lt_succ_iff.1 hlt
          have h1 : x (j + 1) - x k = (x (j + 1) - x j) + (x j - x k) := by abel
          rw [h1]
          exact Submodule.add_mem _ (FM.antitone (hsmono.monotone hkj') (hxstep j)) (ih hkj')
        · have hk : k = j + 1 := le_antisymm hkj hge
          subst hk
          simp
  have hLk : ∀ k, L - x k ∈ FM.fil (s k) := by
    intro k
    have hks : k ≤ s k := le_cofinalSelector A hA k
    have h1 : L - x k = (L - x (s k)) + (x (s k) - x k) := by abel
    rw [h1]
    exact Submodule.add_mem _ (hL (s k)) (htail k (s k) hks)
  refine ⟨L, ?_⟩
  have hzero : f L - y = 0 := by
    refine FN.eq_zero_of_mem_all fun m => ?_
    refine FN.antitone (le_cofinalSelector A hA m) ?_
    have h1 : f L - y = f (L - x m) - (y - f (x m)) := by rw [map_sub]; abel
    rw [h1]
    exact Submodule.sub_mem _ (hmap (s m) ⟨L - x m, hLk m, rfl⟩) (hxy m)
  exact sub_eq_zero.1 hzero

/-- **The cofinal-observer conservativity law.**  A cofinal family of finite-resource observers is
jointly conservative. -/
theorem bijective_of_cofinal_quotient_bijective (FM : LinearFiltration R M)
    (f : M →ₗ[R] N) (FN : LinearFiltration R N) (A : Set ℕ) (hA : ∀ m, ∃ n ∈ A, m ≤ n)
    (hmap : ∀ n, Submodule.map f (FM.fil n) ≤ FN.fil n)
    (hinj : ∀ n ∈ A, ∀ x : M, f x ∈ FN.fil n → x ∈ FM.fil n)
    (hsurj : ∀ n ∈ A, ∀ y : N, ∃ x : M, y - f x ∈ FN.fil n) :
    Function.Bijective f :=
  ⟨injective_of_cofinal_quotient_injective FM f FN A hA hinj,
    surjective_of_cofinal_quotient_bijective FM f FN A hA hmap hinj hsurj⟩

end Sufficiency

/-! ## The countermodel -/

section Necessity

variable (k : Type*) [Field k]

/-- The tail filtration of the full product `∏_{n≥0} k e_n`. -/
def tailFil (n : ℕ) : Submodule k (ℕ → k) where
  carrier := {x | ∀ i < n, x i = 0}
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

@[simp]
theorem mem_tailFil {n : ℕ} {x : ℕ → k} : x ∈ tailFil k n ↔ ∀ i < n, x i = 0 := Iff.rfl

theorem tailFil_antitone : Antitone (tailFil k) := by
  intro m n hmn x hx i hi
  exact hx i (lt_of_lt_of_le hi hmn)

/-- In a Cauchy sequence for the tail filtration, each coordinate is eventually constant. -/
theorem coord_eventually_const {x : ℕ → (ℕ → k)}
    (hx : ∀ n, x (n + 1) - x n ∈ tailFil k n) (i : ℕ) :
    ∀ m, i + 1 ≤ m → x m i = x (i + 1) i := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      have hstep : (x (m + 1) - x m) i = 0 := hx m i (by omega)
      have heq : x (m + 1) i = x m i := by
        simp only [Pi.sub_apply, sub_eq_zero] at hstep
        exact hstep
      rw [heq, ih]

/-- The tail filtration is decreasing, separated and complete. -/
def productFiltration : LinearFiltration k (ℕ → k) where
  fil := tailFil k
  antitone := tailFil_antitone k
  separated := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hall : ∀ n, x ∈ tailFil k n := fun n => (Submodule.mem_iInf _).1 hx n
    have hz : x = 0 := by
      funext i
      exact hall (i + 1) i (Nat.lt_succ_self i)
    simpa using hz
  complete := by
    intro x hx
    refine ⟨fun i => x (i + 1) i, fun n i hi => ?_⟩
    have := coord_eventually_const k hx i n (by omega)
    simp [this]

/-! ### The prolongation and the involution -/

/-- The prolongation `∇ e_n = e_{n+1}`. -/
def prolong : (ℕ → k) →ₗ[k] (ℕ → k) where
  toFun x := fun n => Nat.casesOn n 0 fun m => x m
  map_add' := by intro a b; funext n; cases n <;> simp
  map_smul' := by intro c a; funext n; cases n <;> simp

@[simp] theorem prolong_zero (x : ℕ → k) : prolong k x 0 = 0 := rfl
@[simp] theorem prolong_succ (x : ℕ → k) (n : ℕ) : prolong k x (n + 1) = x n := rfl

/-- The involution `τ e_n = (-1)^n e_n`. -/
def parityInv : (ℕ → k) →ₗ[k] (ℕ → k) where
  toFun x := fun n => (-1 : k) ^ n * x n
  map_add' := by intro a b; funext n; simp [mul_add]
  map_smul' := by intro c a; funext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
                  ring

@[simp] theorem parityInv_apply (x : ℕ → k) (n : ℕ) :
    parityInv k x n = (-1 : k) ^ n * x n := rfl

/-- The involution squares to the identity. -/
theorem parityInv_involutive (x : ℕ → k) : parityInv k (parityInv k x) = x := by
  funext n
  simp [← mul_assoc, ← pow_add, ← two_mul, pow_mul]

/-- **`τ ∇ = − ∇ τ`.**  The prolongation anticommutes with the involution. -/
theorem parityInv_comp_prolong :
    (parityInv k).comp (prolong k) = -((prolong k).comp (parityInv k)) := by
  ext x n
  cases n with
  | zero => simp
  | succ m => simp [pow_succ]

/-- The prolongation raises the filtration. -/
theorem prolong_mem (n : ℕ) (x : ℕ → k) (hx : x ∈ tailFil k n) :
    prolong k x ∈ tailFil k (n + 1) := by
  intro i hi
  cases i with
  | zero => rfl
  | succ m => exact hx m (by omega)

/-- The involution preserves the filtration. -/
theorem parityInv_mem (n : ℕ) (x : ℕ → k) (hx : x ∈ tailFil k n) :
    parityInv k x ∈ tailFil k n := by
  intro i hi
  simp [hx i hi]

/-! ### The invisible tail object -/

theorem tailFil_ne_bot (M : ℕ) : tailFil k (M + 1) ≠ ⊥ := by
  intro h
  have hmem : (Pi.single (M + 1) (1 : k)) ∈ tailFil k (M + 1) := by
    intro i hi
    have hne : i ≠ M + 1 := by omega
    simp [hne]
  rw [h, Submodule.mem_bot] at hmem
  have := congrFun hmem (M + 1)
  simp at this

/-- The induced filtration on the tail object is again separated and complete. -/
def tailObjectFiltration (M : ℕ) : LinearFiltration k (tailFil k (M + 1)) where
  fil n := (tailFil k n).comap (tailFil k (M + 1)).subtype
  antitone := by
    intro m n hmn
    exact Submodule.comap_mono (tailFil_antitone k hmn)
  separated := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hall : ∀ n, (x : ℕ → k) ∈ tailFil k n := fun n => (Submodule.mem_iInf _).1 hx n
    have hz : (x : ℕ → k) = 0 := by
      funext i
      exact hall (i + 1) i (Nat.lt_succ_self i)
    simpa using Subtype.ext hz
  complete := by
    intro x hx
    have hx' : ∀ n, (fun j => (x j : ℕ → k)) (n + 1) - (fun j => (x j : ℕ → k)) n
        ∈ tailFil k n := fun n => hx n
    have hLmem : (fun i => (x (i + 1) : ℕ → k) i) ∈ tailFil k (M + 1) := by
      intro i hi
      exact (x (i + 1)).2 i hi
    refine ⟨⟨fun i => (x (i + 1) : ℕ → k) i, hLmem⟩, fun n i hi => ?_⟩
    have hconst := coord_eventually_const (x := fun j => (x j : ℕ → k)) k hx' i n (by omega)
    simp [hconst]

/-- **Necessity.**  For every bound `M` the tail object `K = F^{M+1} X` is a nonzero, complete,
`∇`-stable and `τ`-stable object that every observer of index at most `M` sees as zero.  Its zero
endomorphism satisfies the level-wise injectivity and surjectivity conditions at every level
`N ≤ M` yet is not bijective, so no bounded observer family is jointly conservative. -/
theorem bounded_observer_family_not_conservative (M : ℕ) :
    (tailFil k (M + 1) ≠ ⊥) ∧
      (∀ x ∈ tailFil k (M + 1), prolong k x ∈ tailFil k (M + 1)) ∧
      (∀ x ∈ tailFil k (M + 1), parityInv k x ∈ tailFil k (M + 1)) ∧
      (∀ N ≤ M, ∀ x : tailFil k (M + 1),
        x ∈ (tailObjectFiltration k M).fil (N + 1)) ∧
      ¬ Function.Bijective (0 : tailFil k (M + 1) →ₗ[k] tailFil k (M + 1)) := by
  refine ⟨tailFil_ne_bot k M, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact tailFil_antitone k (Nat.le_succ (M + 1)) (prolong_mem k (M + 1) x hx)
  · intro x hx
    exact parityInv_mem k (M + 1) x hx
  · intro N hN x
    exact tailFil_antitone k (by omega) x.2
  · intro hbij
    obtain ⟨v, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (tailFil_ne_bot k M)
    have : (⟨v, hv.1⟩ : tailFil k (M + 1)) = 0 := by
      have h0 : (0 : tailFil k (M + 1) →ₗ[k] tailFil k (M + 1)) ⟨v, hv.1⟩ = 0 := rfl
      have h0' : (0 : tailFil k (M + 1) →ₗ[k] tailFil k (M + 1)) 0 = 0 := rfl
      exact hbij.1 (h0.trans h0'.symm)
    exact hv.2 (congrArg Subtype.val this)

end Necessity

end HTGeometry.ConstraintRelativity
