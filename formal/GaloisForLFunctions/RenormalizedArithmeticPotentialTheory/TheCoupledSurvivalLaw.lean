import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCountertermRankDichotomy

/-!
# The coupled survival law

The prime place renormalizes by the torsion germ, whose counterterm is the identity: nothing
survives the limit (RBG `torsion_survivalCone_eq`). The report's central conjecture asks whether
coupling the torsion germ to the archimedean germ and the arithmetic point lowers the rank of the
counterterm and lets degree-zero cycles survive. This file answers the question for every coupling.

A **coupled counterterm** on a prime block `V_P = α → ℝ` and a partner block `V_A = β → ℝ` is a
symmetric block matrix `B = [[A, C], [Cᵀ, D]]` (`coupled`). Positivity is the only input.

* **The partner kernel is blind to the coupling** (`coupling_mulVec_eq_zero`): `D w = 0 ⇒ C w = 0`.
  Hence `rank C ≤ rank D` (`rank_coupling_le`).
* **Survival equations** (`mem_survivalCone_coupled_iff`): `(u, w)` survives iff `A u + C w = 0` and
  `Cᵀ u + D w = 0`.
* **Nondegenerate prime block** (`A u = 0 ⇒ u = 0`): no pure prime vector survives
  (`eq_zero_of_inl_mem_survivalCone`), the survival space has dimension at most `#β`
  (`finrank_survival_le_card`), the counterterm has rank at least `#α` (`card_le_rank_coupled`), and
  the prime projection of the survival space has dimension at most `rank D`
  (`finrank_primeSurvival_le_rank`): **a partner pays at most as many prime directions as the rank of
  its own counterterm**.
* **A rank-one partner pays one matched direction** (`coupling_eq_vecMulVec`,
  `dotProduct_self_le_one`, `primeSurvival_rankOne`). With `A = 1` and `D = v vᵀ` the coupling is
  `C = b vᵀ` with `|b| ≤ 1`, and the prime survival is `ℝ b` if `|b| = 1` and `0` otherwise.
* **The torsion germ** (`coupled_torsion_survival`). For every positive regularized family whose
  prime block is the torsion germ, the prime block of its counterterm is a positive multiple of the
  identity, so the counterterm has rank at least the number of orders and the torsion directions
  that survive span at most `rank` of the partner block. Coupled to the archimedean lattice germ
  (counterterm `𝟙𝟙ᵀ`), at most one torsion direction survives (`coupled_lattice_primeSurvival_le_one`).

So under the Abel regulator coupling cannot lower the torsion counterterm rank, and the archimedean
place, whose counterterm has rank one, pays one direction: the matched one.
-/

noncomputable section

open Filter Topology Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open RenormalizedBiarithmeticGeometry

/-! ### Null vectors of a positive symmetric form -/

section Kernel

variable {ι : Type*} [Fintype ι]

theorem quad_eq_dotProduct (B : Matrix ι ι ℝ) (x : ι → ℝ) : quad B x = x ⬝ᵥ (B *ᵥ x) := by
  simp only [quad, dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- A symmetric real matrix with nonnegative form is positive semidefinite. -/
theorem posSemidef_of_quad_nonneg {B : Matrix ι ι ℝ} (hBs : B.IsSymm) (hB : ∀ x, 0 ≤ quad B x) :
    B.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    (by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hBs)
    fun x => by simpa [quad_eq_dotProduct] using hB x

/-- **Null vectors are kernel vectors**: for a symmetric positive form, `quad B x = 0 ↔ B x = 0`. -/
theorem mem_survivalCone_iff_mulVec_eq_zero {B : Matrix ι ι ℝ} (hBs : B.IsSymm)
    (hB : ∀ x, 0 ≤ quad B x) (x : ι → ℝ) : x ∈ survivalCone B ↔ B *ᵥ x = 0 := by
  have h := (posSemidef_of_quad_nonneg hBs hB).dotProduct_mulVec_zero_iff x
  simpa [survivalCone, quad_eq_dotProduct] using h

/-- The survival cone of a symmetric positive counterterm is the kernel subspace. -/
theorem survivalCone_eq_ker {B : Matrix ι ι ℝ} (hBs : B.IsSymm) (hB : ∀ x, 0 ≤ quad B x) :
    survivalCone B = (LinearMap.ker B.mulVecLin : Set (ι → ℝ)) := by
  ext x
  rw [mem_survivalCone_iff_mulVec_eq_zero hBs hB]
  simp

/-- A rank-one matrix acts by the dot product: `(u vᵀ) w = (v · w) u`. -/
theorem vecMulVec_mulVec' {κ : Type*} (u : κ → ℝ) (v w : ι → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  exact sum_congr rfl fun j _ => by ring

end Kernel

/-! ### Coupled counterterms -/

section Coupled

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The **coupled counterterm** with prime block `A`, coupling `C` and partner block `D`. -/
def coupled (A : Matrix α α ℝ) (C : Matrix α β ℝ) (D : Matrix β β ℝ) :
    Matrix (α ⊕ β) (α ⊕ β) ℝ :=
  fromBlocks A C Cᵀ D

/-- The **prime survival**: the projection of the survival space to the prime block. -/
def primeSurvival (A : Matrix α α ℝ) (C : Matrix α β ℝ) (D : Matrix β β ℝ) :
    Submodule ℝ (α → ℝ) :=
  (LinearMap.ker (coupled A C D).mulVecLin).map (LinearMap.funLeft ℝ ℝ Sum.inl)

omit [Fintype α] [Fintype β] in
theorem coupled_isSymm {A : Matrix α α ℝ} {D : Matrix β β ℝ} (hA : A.IsSymm) (hD : D.IsSymm)
    (C : Matrix α β ℝ) : (coupled A C D).IsSymm :=
  IsSymm.fromBlocks hA rfl hD

theorem coupled_mulVec (A : Matrix α α ℝ) (C : Matrix α β ℝ) (D : Matrix β β ℝ) (u : α → ℝ)
    (w : β → ℝ) :
    coupled A C D *ᵥ Sum.elim u w = Sum.elim (A *ᵥ u + C *ᵥ w) (Cᵀ *ᵥ u + D *ᵥ w) := by
  rw [coupled, fromBlocks_mulVec]
  rfl

omit [Fintype α] [Fintype β] in
theorem sum_elim_eq_zero_iff (u : α → ℝ) (w : β → ℝ) :
    Sum.elim u w = 0 ↔ u = 0 ∧ w = 0 := by
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun j => congrFun h (Sum.inr j)⟩
  · rintro ⟨rfl, rfl⟩
    exact Sum.elim_zero_zero

theorem mem_ker_coupled_iff (A : Matrix α α ℝ) (C : Matrix α β ℝ) (D : Matrix β β ℝ)
    (u : α → ℝ) (w : β → ℝ) :
    Sum.elim u w ∈ LinearMap.ker (coupled A C D).mulVecLin ↔
      A *ᵥ u + C *ᵥ w = 0 ∧ Cᵀ *ᵥ u + D *ᵥ w = 0 := by
  rw [LinearMap.mem_ker, mulVecLin_apply, coupled_mulVec, sum_elim_eq_zero_iff]

variable {A : Matrix α α ℝ} {C : Matrix α β ℝ} {D : Matrix β β ℝ}

/-- **Survival equations.** For a positive coupled counterterm, `(u, w)` survives iff
`A u + C w = 0` and `Cᵀ u + D w = 0`. -/
theorem mem_survivalCone_coupled_iff (hA : A.IsSymm) (hD : D.IsSymm)
    (hB : ∀ x, 0 ≤ quad (coupled A C D) x) (u : α → ℝ) (w : β → ℝ) :
    Sum.elim u w ∈ survivalCone (coupled A C D) ↔
      A *ᵥ u + C *ᵥ w = 0 ∧ Cᵀ *ᵥ u + D *ᵥ w = 0 := by
  rw [mem_survivalCone_iff_mulVec_eq_zero (coupled_isSymm hA hD C) hB, ← mulVecLin_apply,
    ← LinearMap.mem_ker, mem_ker_coupled_iff]

/-- **The partner kernel is blind to the coupling**: in a positive coupled counterterm every null
vector of the partner block is annihilated by the coupling. -/
theorem coupling_mulVec_eq_zero (hA : A.IsSymm) (hD : D.IsSymm)
    (hB : ∀ x, 0 ≤ quad (coupled A C D) x) {w : β → ℝ} (hw : D *ᵥ w = 0) : C *ᵥ w = 0 := by
  have hnull : Sum.elim (0 : α → ℝ) w ∈ survivalCone (coupled A C D) := by
    show quad _ _ = 0
    rw [quad_eq_dotProduct, coupled_mulVec, sumElim_dotProduct_sumElim, hw]
    simp
  have h := ((mem_survivalCone_coupled_iff hA hD hB 0 w).mp hnull).1
  simpa using h

/-- `rank C ≤ rank D`: the coupling factors through the range of the partner block. -/
theorem rank_coupling_le (hA : A.IsSymm) (hD : D.IsSymm)
    (hB : ∀ x, 0 ≤ quad (coupled A C D) x) : C.rank ≤ D.rank := by
  have hker : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin := fun w hw => by
    rw [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
    exact coupling_mulVec_eq_zero hA hD hB hw
  have h1 := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have h3 := Submodule.finrank_mono hker
  unfold Matrix.rank
  omega

variable (hAinj : ∀ u, A *ᵥ u = 0 → u = 0)
include hAinj

/-- **No pure prime vector survives** a coupled counterterm with nondegenerate prime block. -/
theorem eq_zero_of_inl_mem_ker {u : α → ℝ}
    (hu : Sum.elim u (0 : β → ℝ) ∈ LinearMap.ker (coupled A C D).mulVecLin) : u = 0 :=
  hAinj u (by simpa using ((mem_ker_coupled_iff A C D u 0).mp hu).1)

theorem eq_zero_of_inl_mem_survivalCone (hA : A.IsSymm) (hD : D.IsSymm)
    (hB : ∀ x, 0 ≤ quad (coupled A C D) x) {u : α → ℝ}
    (hu : Sum.elim u (0 : β → ℝ) ∈ survivalCone (coupled A C D)) : u = 0 :=
  hAinj u (by simpa using ((mem_survivalCone_coupled_iff hA hD hB u 0).mp hu).1)

/-- The survival space projects injectively to the partner block. -/
theorem injective_partnerProjection :
    Function.Injective ((LinearMap.funLeft ℝ ℝ (Sum.inr : β → α ⊕ β)).domRestrict
      (LinearMap.ker (coupled A C D).mulVecLin)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ h0
  have hw : x ∘ Sum.inr = 0 := h0
  have hx' : Sum.elim (x ∘ Sum.inl) (0 : β → ℝ) ∈ LinearMap.ker (coupled A C D).mulVecLin := by
    rw [← hw, Sum.elim_comp_inl_inr]
    exact hx
  have hu := eq_zero_of_inl_mem_ker hAinj hx'
  ext (i | j)
  · exact congrFun hu i
  · exact congrFun hw j

/-- **The survival space has dimension at most `#β`.** -/
theorem finrank_survival_le_card :
    Module.finrank ℝ (LinearMap.ker (coupled A C D).mulVecLin) ≤ Fintype.card β := by
  have h : Module.finrank ℝ (LinearMap.ker (coupled A C D).mulVecLin) ≤
      Module.finrank ℝ (β → ℝ) :=
    LinearMap.finrank_le_finrank_of_injective (injective_partnerProjection hAinj)
  rwa [Module.finrank_fintype_fun_eq_card] at h

/-- **The coupled counterterm has rank at least `#α`**: coupling never lowers the rank of a
nondegenerate prime block. -/
theorem card_le_rank_coupled : Fintype.card α ≤ (coupled A C D).rank := by
  have h1 : Module.finrank ℝ (LinearMap.range (coupled A C D).mulVecLin) +
      Module.finrank ℝ (LinearMap.ker (coupled A C D).mulVecLin) = Module.finrank ℝ (α ⊕ β → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h2 := finrank_survival_le_card (C := C) (D := D) hAinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h1
  unfold Matrix.rank
  omega

/-- **A partner pays at most its rank**: the prime projection of the survival space has dimension
at most the rank of the partner block. -/
theorem finrank_primeSurvival_le_rank (hA : A.IsSymm) (hD : D.IsSymm)
    (hB : ∀ x, 0 ≤ quad (coupled A C D) x) :
    Module.finrank ℝ (primeSurvival A C D) ≤ D.rank := by
  -- `A` maps the prime survival injectively into the range of the coupling.
  have hmaps : (primeSurvival A C D).map A.mulVecLin ≤ LinearMap.range C.mulVecLin := by
    rintro _ ⟨u, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) ∈
        LinearMap.ker (coupled A C D).mulVecLin := by
      rw [Sum.elim_comp_inl_inr]; exact hx
    have h := ((mem_ker_coupled_iff A C D _ _).mp hx').1
    refine ⟨-(x ∘ Sum.inr), ?_⟩
    simp only [mulVecLin_apply, mulVec_neg]
    have : A *ᵥ (x ∘ Sum.inl) = -(C *ᵥ (x ∘ Sum.inr)) := eq_neg_of_add_eq_zero_left h
    exact this.symm
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun u hu => hAinj u hu
  calc Module.finrank ℝ (primeSurvival A C D)
      = Module.finrank ℝ ((primeSurvival A C D).map A.mulVecLin) :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _))
    _ ≤ Module.finrank ℝ (LinearMap.range C.mulVecLin) := Submodule.finrank_mono hmaps
    _ = C.rank := rfl
    _ ≤ D.rank := rank_coupling_le hA hD hB

end Coupled

/-! ### A rank-one partner pays one matched direction -/

section RankOne

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- **A coupling to a rank-one partner is rank one along the partner vector**: if
`[[1, C], [Cᵀ, v vᵀ]]` is positive, then `C = b vᵀ` with `b = C v/(v · v)`. -/
theorem coupling_eq_vecMulVec {C : Matrix α β ℝ} {v : β → ℝ} (hv : v ≠ 0)
    (hB : ∀ x, 0 ≤ quad (coupled 1 C (vecMulVec v v)) x) :
    C = vecMulVec ((v ⬝ᵥ v)⁻¹ • (C *ᵥ v)) v := by
  classical
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro h
    exact hv (dotProduct_self_eq_zero.mp h)
  have hD : (vecMulVec v v).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_vecMulVec]
  ext i j
  -- `w = e_j − (v_j/(v·v)) v` is orthogonal to `v`, hence killed by `C`.
  set w : β → ℝ := Pi.single j 1 - (v j / (v ⬝ᵥ v)) • v
  have hvw : v ⬝ᵥ w = 0 := by
    simp only [w, dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
    field_simp
    ring
  have hCw : C *ᵥ w = 0 :=
    coupling_mulVec_eq_zero isSymm_one hD hB (by rw [vecMulVec_mulVec', hvw, zero_smul])
  have hi := congrFun hCw i
  simp only [w, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mulVec_single_one, Pi.zero_apply] at hi
  simp only [vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul]
  have : C i j = v j / (v ⬝ᵥ v) * (C *ᵥ v) i := by
    rw [show (C.col j) i = C i j from rfl] at hi
    linarith
  rw [this]
  field_simp

/-- The form of the matched coupling: `|u|² + 2(b · u)(v · w) + (v · w)²`. -/
theorem quad_coupled_rankOne (b u : α → ℝ) (v w : β → ℝ) :
    quad (coupled 1 (vecMulVec b v) (vecMulVec v v)) (Sum.elim u w) =
      u ⬝ᵥ u + 2 * (b ⬝ᵥ u) * (v ⬝ᵥ w) + (v ⬝ᵥ w) ^ 2 := by
  rw [quad_eq_dotProduct, coupled_mulVec, sumElim_dotProduct_sumElim, transpose_vecMulVec,
    vecMulVec_mulVec', vecMulVec_mulVec', vecMulVec_mulVec', one_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm u b, dotProduct_comm w v]
  ring

/-- **Cauchy–Schwarz for the matched coupling**: positivity of `[[1, b vᵀ], [v bᵀ, v vᵀ]]` forces
`b · b ≤ 1`. -/
theorem dotProduct_self_le_one {b : α → ℝ} {v : β → ℝ} (hv : v ≠ 0)
    (hB : ∀ x, 0 ≤ quad (coupled 1 (vecMulVec b v) (vecMulVec v v)) x) : b ⬝ᵥ b ≤ 1 := by
  have hvv : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  -- test vector `(b, −|b|² v/|v|²)`: the form is `|b|² − |b|⁴`.
  have h := hB (Sum.elim b ((-((b ⬝ᵥ b) / (v ⬝ᵥ v))) • v))
  rw [quad_coupled_rankOne, dotProduct_smul, smul_eq_mul,
    show -((b ⬝ᵥ b) / (v ⬝ᵥ v)) * (v ⬝ᵥ v) = -(b ⬝ᵥ b) by field_simp] at h
  have hb0 : 0 ≤ b ⬝ᵥ b := by simpa using dotProduct_self_star_nonneg b
  rcases hb0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; norm_num

/-- **A rank-one partner pays exactly the matched direction.** For a positive coupled counterterm
`[[1, b vᵀ], [v bᵀ, v vᵀ]]` with `v ≠ 0`, the prime survival is the line `ℝ b` if `|b| = 1` and `0`
otherwise. -/
theorem primeSurvival_rankOne {b : α → ℝ} {v : β → ℝ} (hv : v ≠ 0) :
    primeSurvival 1 (vecMulVec b v) (vecMulVec v v) =
      if b ⬝ᵥ b = 1 then Submodule.span ℝ {b} else ⊥ := by
  classical
  have hvv : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  -- the survival equations of the rank-one coupling
  have hker : ∀ u w, Sum.elim u w ∈ LinearMap.ker (coupled 1 (vecMulVec b v) (vecMulVec v v)).mulVecLin ↔
      u = -(v ⬝ᵥ w) • b ∧ b ⬝ᵥ u + v ⬝ᵥ w = 0 := by
    intro u w
    rw [mem_ker_coupled_iff, transpose_vecMulVec, vecMulVec_mulVec', vecMulVec_mulVec',
      vecMulVec_mulVec', one_mulVec, ← add_smul]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h1, ?_⟩
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hv
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h1, neg_smul, neg_add_cancel], by rw [h2, zero_smul]⟩
  have hmem : ∀ u, u ∈ primeSurvival 1 (vecMulVec b v) (vecMulVec v v) ↔
      ∃ w : β → ℝ, u = -(v ⬝ᵥ w) • b ∧ b ⬝ᵥ u + v ⬝ᵥ w = 0 := by
    intro u
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x ∘ Sum.inr, (hker (x ∘ Sum.inl) (x ∘ Sum.inr)).mp ?_⟩
      rw [Sum.elim_comp_inl_inr]
      exact hx
    · rintro ⟨w, hw⟩
      exact ⟨Sum.elim u w, (hker u w).mpr hw, rfl⟩
  ext u
  rw [hmem]
  split_ifs with hb
  · rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨w, h1, -⟩
      exact ⟨-(v ⬝ᵥ w), h1.symm⟩
    · rintro ⟨s, rfl⟩
      refine ⟨(-(s / (v ⬝ᵥ v))) • v, ?_, ?_⟩
      · rw [dotProduct_smul, smul_eq_mul]
        congr 1
        field_simp
      · rw [dotProduct_smul, dotProduct_smul, hb, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
  · rw [Submodule.mem_bot]
    constructor
    · rintro ⟨w, h1, h2⟩
      -- `b · u = −(v · w)|b|²`, so `(v · w)(1 − |b|²) = 0`.
      rw [h1, dotProduct_smul, smul_eq_mul] at h2
      have hvw : v ⬝ᵥ w = 0 := by
        have : (v ⬝ᵥ w) * (1 - b ⬝ᵥ b) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linarith) hb
      rw [h1, hvw, neg_zero, zero_smul]
    · rintro rfl
      exact ⟨0, by simp, by simp⟩

end RankOne

/-! ### The torsion germ coupled to a partner -/

section Torsion

open ArithmeticEffectivityTheory

variable {S : Finset ℕ} {β : Type*} [Fintype β]

/-- The prime block of a matrix on `S ⊕ β`. -/
def primeBlock (B : Matrix (S ⊕ β) (S ⊕ β) ℝ) : Matrix S S ℝ := B.toBlocks₁₁

/-- The partner block of a matrix on `S ⊕ β`. -/
def partnerBlock (B : Matrix (S ⊕ β) (S ⊕ β) ℝ) : Matrix β β ℝ := B.toBlocks₂₂

/-- A counterterm of a symmetric family is symmetric. -/
theorem counterterm_isSymm {ι : Type*} {Q : ℝ → Matrix ι ι ℝ} {s : ℝ → ℝ} {B L : Matrix ι ι ℝ}
    (hQs : ∀ r, (Q r).IsSymm) (hs : Tendsto s (𝓝[<] 1) atTop)
    (hlim : ∀ i j, Tendsto (fun r => Q r i j - s r * B i j) (𝓝[<] 1) (𝓝 (L i j))) :
    B.IsSymm := by
  ext i j
  -- `s (B i j − B j i)` converges while `s → ∞`, so `B i j = B j i`.
  have hconv : Tendsto (fun r => s r * (B i j - B j i)) (𝓝[<] 1) (𝓝 (L j i - L i j)) := by
    refine ((hlim j i).sub (hlim i j)).congr fun r => ?_
    have hQ : Q r j i = Q r i j := by
      have := congrFun (congrFun (hQs r) i) j
      simpa [transpose_apply] using this
    rw [hQ]
    ring
  have hzero : B i j - B j i = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact not_tendsto_nhds_of_tendsto_atBot (hs.atTop_mul_const_of_neg hneg) _ hconv
    · exact not_tendsto_nhds_of_tendsto_atTop (hs.atTop_mul_const hpos) _ hconv
  simp only [transpose_apply]
  linarith

omit [Fintype β] in
/-- A matrix on `S ⊕ β` is the coupled counterterm of its blocks, once it is symmetric. -/
theorem eq_coupled_of_isSymm {B : Matrix (S ⊕ β) (S ⊕ β) ℝ} (hB : B.IsSymm) :
    B = coupled (primeBlock B) B.toBlocks₁₂ (partnerBlock B) := by
  have h21 : B.toBlocks₂₁ = B.toBlocks₁₂ᵀ := by
    ext i j
    simp only [toBlocks₂₁, toBlocks₁₂, transpose_apply, of_apply]
    exact (congrFun (congrFun hB (Sum.inr i)) (Sum.inl j)).symm
  rw [coupled, primeBlock, partnerBlock, ← h21, fromBlocks_toBlocks]

omit [Fintype β] in
/-- **The prime block of a coupled torsion counterterm is a positive multiple of the identity.**
If a regularized family on `S ⊕ β` has the torsion germ as prime block and divergence `s → ∞`, the
prime block of its counterterm is `c · 1` with `c > 0`. -/
theorem primeBlock_eq_smul_one (hS : ∀ n ∈ S, 0 < n) (hne : S.Nonempty)
    {Q : ℝ → Matrix (S ⊕ β) (S ⊕ β) ℝ} {s : ℝ → ℝ} {B L : Matrix (S ⊕ β) (S ⊕ β) ℝ}
    (hprime : ∀ r m n, Q r (Sum.inl m) (Sum.inl n) = torsionGerm S r m n)
    (hs : Tendsto s (𝓝[<] 1) atTop)
    (hlim : ∀ i j, Tendsto (fun r => Q r i j - s r * B i j) (𝓝[<] 1) (𝓝 (L i j))) :
    ∃ c : ℝ, 0 < c ∧ primeBlock B = c • (1 : Matrix S S ℝ) := by
  classical
  obtain ⟨n₀, hn₀⟩ := hne
  set i₀ : S := ⟨n₀, hn₀⟩
  have hblock : ∀ m n : S, Tendsto (fun r => torsionGerm S r m n - s r * primeBlock B m n)
      (𝓝[<] 1) (𝓝 (L (Sum.inl m) (Sum.inl n))) := fun m n => by
    simpa [primeBlock, toBlocks₁₁, hprime] using hlim (Sum.inl m) (Sum.inl n)
  obtain ⟨c, hc, hBc⟩ := counterterm_eq_smul hblock (torsionGerm_regularized hS).2 hs
    (i₀ := i₀) (j₀ := i₀) (by simp)
  refine ⟨c, ?_, hBc⟩
  -- `c ≥ 0` from the ratio of two divergences, `c ≠ 0` since the torsion diagonal diverges.
  have hc0 : 0 ≤ c := by
    refine ge_of_tendsto hc ?_
    filter_upwards [hs.eventually_gt_atTop 0,
      tendsto_neg_log_abs_one_sub.eventually_gt_atTop 0] with r hr1 hr2
    exact div_nonneg hr2.le hr1.le
  rcases hc0.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hdiag := hblock i₀ i₀
    rw [hBc, ← hzero] at hdiag
    simp only [zero_smul, Matrix.zero_apply, mul_zero, sub_zero] at hdiag
    have htor := (torsionGerm_regularized hS).2 i₀ i₀
    simp only [Matrix.one_apply_eq, mul_one] at htor
    -- `−log |1 − r| = G_r − (G_r + log |1 − r|)` would converge.
    have hconv := hdiag.sub htor
    have hdiv : Tendsto (fun r => torsionGerm S r i₀ i₀ - (torsionGerm S r i₀ i₀ -
        -Real.log |1 - r|)) (𝓝[<] 1) atTop :=
      tendsto_neg_log_abs_one_sub.congr fun r => by ring
    exact not_tendsto_nhds_of_tendsto_atTop hdiv _ hconv

/-- **The coupled survival law for the torsion germ.** Let `Q_r` be a positive symmetric regularized
family on the orders `S` and a partner block `β`, whose prime block is the torsion germ, with
divergence `s → ∞` and counterterm `B`. Then no pure torsion vector survives, the counterterm has rank
at least `#S`, and the torsion directions in the survival cone span at most `rank` of the partner
block of `B`. -/
theorem coupled_torsion_survival (hS : ∀ n ∈ S, 0 < n) (hne : S.Nonempty)
    {Q : ℝ → Matrix (S ⊕ β) (S ⊕ β) ℝ} {s : ℝ → ℝ} {B L : Matrix (S ⊕ β) (S ⊕ β) ℝ}
    (hQs : ∀ r, (Q r).IsSymm) (hQ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ x, 0 ≤ quad (Q r) x)
    (hprime : ∀ r m n, Q r (Sum.inl m) (Sum.inl n) = torsionGerm S r m n)
    (hs : Tendsto s (𝓝[<] 1) atTop)
    (hlim : ∀ i j, Tendsto (fun r => Q r i j - s r * B i j) (𝓝[<] 1) (𝓝 (L i j))) :
    (∀ u : S → ℝ, Sum.elim u (0 : β → ℝ) ∈ survivalCone B → u = 0) ∧
      S.card ≤ B.rank ∧
      Module.finrank ℝ (primeSurvival (primeBlock B) B.toBlocks₁₂ (partnerBlock B)) ≤
        (partnerBlock B).rank := by
  classical
  have hBs := counterterm_isSymm hQs hs hlim
  have hBpos := counterterm_nonneg hQ hs hlim
  obtain ⟨c, hc, hBc⟩ := primeBlock_eq_smul_one hS hne hprime hs hlim
  have hB : B = coupled (primeBlock B) B.toBlocks₁₂ (partnerBlock B) := eq_coupled_of_isSymm hBs
  have hAs : (primeBlock B).IsSymm := by rw [hBc]; exact (isSymm_one).smul c
  have hDs : (partnerBlock B).IsSymm := by
    ext i j
    have := congrFun (congrFun hBs (Sum.inr i)) (Sum.inr j)
    simpa [transpose_apply, partnerBlock, toBlocks₂₂] using this
  have hpos : ∀ x, 0 ≤ quad (coupled (primeBlock B) B.toBlocks₁₂ (partnerBlock B)) x := by
    rw [← hB]; exact hBpos
  have hinj : ∀ u, primeBlock B *ᵥ u = 0 → u = 0 := fun u hu => by
    rw [hBc, smul_mulVec, one_mulVec] at hu
    exact (smul_eq_zero.mp hu).resolve_left hc.ne'
  refine ⟨fun u hu => ?_, ?_, finrank_primeSurvival_le_rank hinj hAs hDs hpos⟩
  · rw [hB] at hu
    exact eq_zero_of_inl_mem_survivalCone hinj hAs hDs hpos hu
  · have h := card_le_rank_coupled (C := B.toBlocks₁₂) (D := partnerBlock B) hinj
    rw [← hB, Fintype.card_coe] at h
    exact h

/-- **Coupled to the archimedean germ, at most one torsion direction survives.** If the partner
block of the counterterm is a multiple of `𝟙𝟙ᵀ` — the counterterm of the lattice germ — the torsion
survival has dimension at most one. -/
theorem coupled_lattice_primeSurvival_le_one (hS : ∀ n ∈ S, 0 < n) (hne : S.Nonempty)
    {k : ℕ} {Q : ℝ → Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ} {s : ℝ → ℝ}
    {B L : Matrix (S ⊕ Fin k) (S ⊕ Fin k) ℝ}
    (hQs : ∀ r, (Q r).IsSymm) (hQ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ x, 0 ≤ quad (Q r) x)
    (hprime : ∀ r m n, Q r (Sum.inl m) (Sum.inl n) = torsionGerm S r m n)
    (hs : Tendsto s (𝓝[<] 1) atTop)
    (hlim : ∀ i j, Tendsto (fun r => Q r i j - s r * B i j) (𝓝[<] 1) (𝓝 (L i j)))
    {a : ℝ} (hpartner : partnerBlock B = a • latticeCounterterm k) :
    Module.finrank ℝ (primeSurvival (primeBlock B) B.toBlocks₁₂ (partnerBlock B)) ≤ 1 := by
  refine (coupled_torsion_survival hS hne hQs hQ hprime hs hlim).2.2.trans ?_
  rw [hpartner, latticeCounterterm]
  have h : a • vecMulVec (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => (1 : ℝ)) =
      vecMulVec (fun _ : Fin k => a) (fun _ : Fin k => (1 : ℝ)) := by
    ext i j
    simp [vecMulVec]
  rw [h]
  exact rank_vecMulVec_le _ _

end Torsion

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
