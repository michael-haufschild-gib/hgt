import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Invariant Hermitian forms on the zero algebra of `Ξ`

The zero algebra `A = O/(Ξ)` on finitely supported data is the direct sum of the jet spaces
`ℂ[ε]/(ε^{m_ρ})` at the zeros `ρ` of `Ξ` (multiplicity `m_ρ`).  Multiplication by `q^{iz}`,
`q ∈ ℚ_{>0}`, acts on the jet at `ρ` by the character `q^{iρ}` times the unipotent operator
`exp(i ε log q)`.

* `invariantForm_eq_zero_of_ne_conj` (support law): an invariant Hermitian form pairs the jets at
  `ρ` and `σ` only when `σ = conj ρ`.
* `posDef_invariantForm_real_simple`: a positive-definite invariant form forces every point to be
  real and every multiplicity to be one; `exists_posDef_invariantForm` is the converse.
* `invariantForm_higherJet_radical`: on a real point, a positive semidefinite invariant form
  vanishes on every jet of order `≥ 1`; `valueForm` (`F ↦ Σ |F(ρ)|²`) is a positive semidefinite
  invariant form, so "sees only the values" is attained.
* `exists_posDef_invariantForm_XiC_iff`: a positive-definite invariant form on the zero algebra of
  `Ξ` exists iff RH holds and every zero of `Ξ` is simple.
-/

open Complex
open scoped Real

namespace RHTower.ZeroAlgebraInvariantForms

noncomputable section

variable {ι : Type*}

/-! ### The jet model -/

/-- Basis labels `(ρ, k)`, `k < m_ρ`, of the jet spaces. -/
abbrev JetIndex (m : ι → ℕ) := Σ i, Fin (m i)

/-- The zero algebra on finitely supported jet data. -/
abbrev ZeroAlgebra (m : ι → ℕ) := JetIndex m →₀ ℂ

/-- The coefficient of `ε^n` in the jet of `e^{iaz}` at `ρ`. -/
def jetCoeff (ρ : ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (I*a*ρ)*(I*a)^n/(n.factorial : ℂ)

/-- Multiplication by `e^{iaz}` on the basis jet `ε^j` at the point `i`. -/
def actBasis (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) (p : JetIndex m) : ZeroAlgebra m :=
  ∑ k : Fin (m p.1), if p.2≤k then Finsupp.single ⟨p.1, k⟩ (jetCoeff (ρ p.1) a ((k:ℕ)-(p.2:ℕ)))
    else 0

/-- The action of `M_q`, `a = log q`, on the zero algebra. -/
def act (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) : ZeroAlgebra m →ₗ[ℂ] ZeroAlgebra m :=
  Finsupp.linearCombination ℂ (actBasis ρ m a)

/-- An `M`-invariant Hermitian form on the zero algebra. -/
structure InvariantForm (ρ : ι → ℂ) (m : ι → ℕ) where
  /-- The sesquilinear form. -/
  form : ZeroAlgebra m →ₗ⋆[ℂ] ZeroAlgebra m →ₗ[ℂ] ℂ
  /-- Hermitian symmetry. -/
  hermitian : ∀ x y, starRingEnd ℂ (form x y)=form y x
  /-- Invariance under every `M_q`, `q ∈ ℚ_{>0}`. -/
  invariant : ∀ q : ℚ, 0<q → ∀ x y,
    form (act ρ m (Real.log q) x) (act ρ m (Real.log q) y)=form x y

/-- The basis jet `ε^k` at the point `i`. -/
def e {m : ι → ℕ} (i : ι) (k : Fin (m i)) : ZeroAlgebra m := Finsupp.single ⟨i, k⟩ 1

theorem act_e (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) (i : ι) (k : Fin (m i)) :
    act ρ m a (e i k)=∑ l : Fin (m i), if k≤l then jetCoeff (ρ i) a ((l:ℕ)-(k:ℕ)) • e i l else 0 := by
  rw [act, e, Finsupp.linearCombination_single, one_smul, actBasis]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [e, Finsupp.smul_single, smul_eq_mul, mul_one]
  · rfl

theorem jetCoeff_zero (ρ : ℂ) (a : ℝ) : jetCoeff ρ a 0=Complex.exp (I*a*ρ) := by
  simp [jetCoeff]

/-- On the top jet the action is the character `e^{iaρ}`. -/
theorem act_e_top (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) (i : ι) (k : Fin (m i))
    (hk : (k:ℕ)+1=m i) : act ρ m a (e i k)=Complex.exp (I*a*ρ i) • e i k := by
  rw [act_e, Finset.sum_eq_single k]
  · rw [if_pos le_rfl, Nat.sub_self, jetCoeff_zero]
  · intro l _ hlk
    rw [if_neg]
    intro hkl
    have : (l:ℕ)≤k := by have := l.isLt; omega
    exact hlk (Fin.ext (le_antisymm this hkl))
  · intro h; exact absurd (Finset.mem_univ k) h

/-- On the next-to-top jet: `ε^{m-2} ↦ e^{iaρ}(ε^{m-2} + i a ε^{m-1})`. -/
theorem act_e_second (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) (i : ι) (k k' : Fin (m i))
    (hk : (k:ℕ)+1=k') (hk' : (k':ℕ)+1=m i) :
    act ρ m a (e i k)=Complex.exp (I*a*ρ i) • (e i k+(I*a) • e i k') := by
  rw [act_e]
  have hkk' : k≠k' := fun h => by rw [h] at hk; omega
  rw [Finset.sum_eq_add_of_mem k k' (Finset.mem_univ _) (Finset.mem_univ _) hkk']
  · rw [if_pos le_rfl, if_pos (show k≤k' by rw [Fin.le_def]; omega), Nat.sub_self, jetCoeff_zero,
      show (k':ℕ)-(k:ℕ)=1 by omega, smul_add, smul_smul]
    congr 1
    simp [jetCoeff]
  · intro l _ hl
    rw [if_neg]
    intro hkl
    have hl1 : (l:ℕ)≠k := fun h => hl.1 (Fin.ext h)
    have hl2 : (l:ℕ)≠k' := fun h => hl.2 (Fin.ext h)
    have := l.isLt
    rw [Fin.le_def] at hkl
    omega

/-! ### Characters at rational points -/

/-- A nonzero frequency is detected by some rational `q`: `q^{iw} ≠ 1`. -/
theorem exists_rat_exp_ne_one {w : ℂ} (hw : w≠0) :
    ∃ q : ℚ, 0<q ∧ Complex.exp (I*(Real.log q : ℂ)*w)≠1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hcon 2 (by norm_num))
  obtain ⟨n', hn'⟩ := Complex.exp_eq_one_iff.mp (hcon 3 (by norm_num))
  have hl2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0:ℝ)<Real.log 3 := Real.log_pos (by norm_num)
  have hπ := Real.pi_pos
  push_cast at hn hn'
  have hw2 : (Real.log 2 : ℂ)*w=2*π*n := by
    have := congrArg (fun z => z/I) hn
    field_simp at this
    linear_combination this
  have hw3 : (Real.log 3 : ℂ)*w=2*π*n' := by
    have := congrArg (fun z => z/I) hn'
    field_simp at this
    linear_combination this
  -- the two equations force `n' log 2 = n log 3`
  have hcross : ((n':ℝ)*Real.log 2 : ℂ)=((n:ℝ)*Real.log 3 : ℂ) := by
    have h2C : (Real.log 2 : ℂ)≠0 := by exact_mod_cast hl2.ne'
    have h3C : (Real.log 3 : ℂ)≠0 := by exact_mod_cast hl3.ne'
    have hπC : (π : ℂ)≠0 := by exact_mod_cast hπ.ne'
    push_cast
    apply mul_left_cancel₀ (show (2*π : ℂ)≠0 by simp [hπC])
    linear_combination (Real.log 3 : ℂ)*hw2-(Real.log 2 : ℂ)*hw3
  have hcrossR : (n':ℝ)*Real.log 2=(n:ℝ)*Real.log 3 := by exact_mod_cast hcross
  have hn0 : n≠0 := by
    intro h0
    rw [h0] at hw2
    simp at hw2
    exact hw (hw2.resolve_left (by exact_mod_cast hl2.ne'))
  -- `2^{n'} = 3^{n}` with `n ≠ 0` is impossible
  have key : ∀ a b : ℕ, 0<b → (a:ℝ)*Real.log 2=(b:ℝ)*Real.log 3 → False := by
    intro a b hb hab
    have h := congrArg Real.exp hab
    rw [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity)] at h
    have hnat : 2^a=3^b := by exact_mod_cast h
    have h3 : ¬ 2∣3^b := by
      intro hd
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd)
      omega
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, pow_zero] at hnat
      have : 1<3^b := Nat.one_lt_pow hb.ne' (by norm_num)
      omega
    · exact h3 (hnat ▸ dvd_pow_self 2 ha.ne')
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · apply key (-n').toNat (-n).toNat (by omega)
    have h1 : ((-n').toNat : ℝ)=-(n':ℝ) := by
      have : 0≤-n' := by
        by_contra hc
        have : 0<(n':ℝ) := by exact_mod_cast (show 0<n' by omega)
        have : (n:ℝ)<0 := by exact_mod_cast hneg
        nlinarith
      rw [show ((-n').toNat : ℝ)=((-n').toNat : ℤ) by norm_cast, Int.toNat_of_nonneg this]
      push_cast; ring
    have h2 : ((-n).toNat : ℝ)=-(n:ℝ) := by
      rw [show ((-n).toNat : ℝ)=((-n).toNat : ℤ) by norm_cast, Int.toNat_of_nonneg (by omega)]
      push_cast; ring
    rw [h1, h2]
    linarith
  · apply key n'.toNat n.toNat (by omega)
    have h1 : (n'.toNat : ℝ)=(n':ℝ) := by
      have : 0≤n' := by
        by_contra hc
        have : (n':ℝ)<0 := by exact_mod_cast (show n'<0 by omega)
        have : 0<(n:ℝ) := by exact_mod_cast hpos
        nlinarith
      rw [show (n'.toNat : ℝ)=(n'.toNat : ℤ) by norm_cast, Int.toNat_of_nonneg this]
    have h2 : (n.toNat : ℝ)=(n:ℝ) := by
      rw [show (n.toNat : ℝ)=(n.toNat : ℤ) by norm_cast, Int.toNat_of_nonneg (by omega)]
    rw [h1, h2]
    exact hcrossR

theorem conj_exp_mul_exp (ρ σ : ℂ) (a : ℝ) :
    starRingEnd ℂ (Complex.exp (I*a*ρ))*Complex.exp (I*a*σ)=
      Complex.exp (I*(a:ℂ)*(σ-starRingEnd ℂ ρ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ### The support law -/

/-- **Support law.**  An invariant form pairs the jets at `i` and `j` only when `ρ_j = conj ρ_i`. -/
theorem invariantForm_eq_zero_of_ne_conj {ρ : ι → ℂ} {m : ι → ℕ} (H : InvariantForm ρ m)
    {i j : ι} (hij : ρ j≠starRingEnd ℂ (ρ i)) (k : Fin (m i)) (l : Fin (m j)) :
    H.form (e i k) (e j l)=0 := by
  obtain ⟨q, hq, hne⟩ := exists_rat_exp_ne_one (sub_ne_zero.mpr hij)
  -- downward induction on the distance to the top jets
  suffices hsuff : ∀ d : ℕ, ∀ k : Fin (m i), ∀ l : Fin (m j),
      (m i-1-(k:ℕ))+(m j-1-(l:ℕ))=d → H.form (e i k) (e j l)=0 by
    exact hsuff _ k l rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro k l hd
  have hinv := H.invariant q hq (e i k) (e j l)
  rw [act_e, act_e, map_sum] at hinv
  simp only [LinearMap.sum_apply, map_sum] at hinv
  -- every term other than (k, l) has a smaller distance
  have hrest : ∀ k' : Fin (m i), ∀ l' : Fin (m j), (k', l')≠(k, l) →
      (H.form (if k≤k' then jetCoeff (ρ i) (Real.log q) ((k':ℕ)-(k:ℕ)) • e i k' else 0))
        (if l≤l' then jetCoeff (ρ j) (Real.log q) ((l':ℕ)-(l:ℕ)) • e j l' else 0)=0 := by
    intro k' l' hne'
    by_cases hk' : k≤k'
    · by_cases hl' : l≤l'
      · have hlt : (m i-1-(k':ℕ))+(m j-1-(l':ℕ))<d := by
          have hk'' : (k:ℕ)≤k' := hk'
          have hl'' : (l:ℕ)≤l' := hl'
          have hor : (k:ℕ)<k' ∨ (l:ℕ)<l' := by
            by_contra hc
            push Not at hc
            exact hne' (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
          have := k'.isLt
          have := l'.isLt
          omega
        have h0 := ih _ hlt k' l' rfl
        rw [if_pos hk', if_pos hl', map_smulₛₗ, map_smul, LinearMap.smul_apply, h0, smul_zero,
          smul_zero]
      · rw [if_neg hl', map_zero]
    · rw [if_neg hk', map_zero, LinearMap.zero_apply]
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l] at hinv
  · rw [if_pos le_rfl, if_pos le_rfl, Nat.sub_self, Nat.sub_self, jetCoeff_zero, jetCoeff_zero,
      map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul,
      conj_exp_mul_exp] at hinv
    have hfac : (Complex.exp (I*(Real.log q : ℂ)*(ρ j-starRingEnd ℂ (ρ i)))-1)*
        H.form (e i k) (e j l)=0 := by
      rw [sub_mul, one_mul, hinv, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  · intro l' _ hl'
    exact hrest k l' (fun h => hl' (congrArg Prod.snd h))
  · intro h; exact absurd (Finset.mem_univ l) h
  · intro k' _ hk'
    rw [← map_sum]
    have : ∀ l' : Fin (m j), (H.form (if k≤k' then jetCoeff (ρ i) (Real.log q) ((k':ℕ)-(k:ℕ)) •
        e i k' else 0)) (if l≤l' then jetCoeff (ρ j) (Real.log q) ((l':ℕ)-(l:ℕ)) • e j l' else 0)=0 :=
      fun l' => hrest k' l' (fun h => hk' (congrArg Prod.fst h))
    simp only [this, Finset.sum_const_zero]
    rw [map_sum]
    exact Finset.sum_eq_zero fun l' _ => this l'
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Positive-definite invariant forms -/

/-- A positive-definite invariant form forces every point to be real and every multiplicity to be
one. -/
theorem posDef_invariantForm_real_simple {ρ : ι → ℂ} {m : ι → ℕ} (H : InvariantForm ρ m)
    (hpos : ∀ x : ZeroAlgebra m, x≠0 → 0<(H.form x x).re) (i : ι) (hm : 1≤m i) :
    (ρ i).im=0 ∧ m i=1 := by
  have he : ∀ k : Fin (m i), e i k≠0 := fun k h => by
    have := congrArg (fun f : ZeroAlgebra m => f ⟨i, k⟩) h
    simp [e] at this
  -- reality from the top jet
  let top : Fin (m i) := ⟨m i-1, by omega⟩
  have hreal : (ρ i).im=0 := by
    have hinv := H.invariant 2 (by norm_num) (e i top) (e i top)
    rw [act_e_top ρ m _ i top (by simp [top]; omega), map_smulₛₗ, map_smul,
      LinearMap.smul_apply, smul_smul, smul_eq_mul] at hinv
    have hv := hpos _ (he top)
    have hne : H.form (e i top) (e i top)≠0 := fun h0 => by rw [h0] at hv; simp at hv
    have hone := mul_right_cancel₀ hne (hinv.trans (one_mul _).symm)
    rw [conj_exp_mul_exp] at hone
    have hnorm := congrArg (‖·‖) hone
    simp only [norm_one, Complex.norm_exp] at hnorm
    have hre : (I*((Real.log ((2:ℚ):ℝ) : ℝ) : ℂ)*(ρ i-starRingEnd ℂ (ρ i))).re=
        2*Real.log 2*(ρ i).im := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hre, Real.exp_eq_one_iff] at hnorm
    have hl2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  refine ⟨hreal, ?_⟩
  by_contra hm1
  have hm2 : 2≤m i := by omega
  let k : Fin (m i) := ⟨m i-2, by omega⟩
  let k' : Fin (m i) := ⟨m i-1, by omega⟩
  have hunit : ∀ a : ℝ, starRingEnd ℂ (Complex.exp (I*a*ρ i))*Complex.exp (I*a*ρ i)=1 := by
    intro a
    rw [conj_exp_mul_exp]
    have : ρ i-starRingEnd ℂ (ρ i)=0 := by
      apply Complex.ext <;> simp [hreal]
    rw [this, mul_zero, Complex.exp_zero]
  have hquad : ∀ q : ℚ, 0<q →
      (starRingEnd ℂ (I*(Real.log q : ℂ)))*H.form (e i k') (e i k)+
        (I*(Real.log q : ℂ))*H.form (e i k) (e i k')+
        (starRingEnd ℂ (I*(Real.log q : ℂ)))*(I*(Real.log q : ℂ))*H.form (e i k') (e i k')=0 := by
    intro q hq
    have hinv := H.invariant q hq (e i k) (e i k)
    rw [act_e_second ρ m _ i k k' (by simp [k, k']; omega) (by simp [k']; omega)] at hinv
    simp only [map_smulₛₗ, map_add, map_smul, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul] at hinv
    have hu := hunit (Real.log q)
    linear_combination hinv-
      (H.form (e i k) (e i k)+starRingEnd ℂ (I*(Real.log q : ℂ))*H.form (e i k') (e i k)+
        I*(Real.log q : ℂ)*H.form (e i k) (e i k')+
        starRingEnd ℂ (I*(Real.log q : ℂ))*(I*(Real.log q : ℂ))*H.form (e i k') (e i k'))*hu
  have h2 := hquad 2 (by norm_num)
  have h4 := hquad 4 (by norm_num)
  have hlog4 : Real.log ((4:ℚ):ℝ)=2*Real.log ((2:ℚ):ℝ) := by
    rw [show ((4:ℚ):ℝ)=((2:ℚ):ℝ)^2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4] at h4
  set L := Real.log ((2:ℚ):ℝ) with hL
  have hL0 : L≠0 := by
    rw [hL]; exact (Real.log_pos (by norm_num)).ne'
  have hconj : starRingEnd ℂ (I*(L : ℂ))=-(I*(L : ℂ)) := by simp
  have hconj2 : starRingEnd ℂ (I*((2*L : ℝ) : ℂ))=-(I*((2*L : ℝ) : ℂ)) := by simp
  rw [hconj] at h2
  rw [hconj2] at h4
  push_cast at h4
  have hII : I*I=-1 := Complex.I_mul_I
  have hd : (L:ℂ)^2*H.form (e i k') (e i k')=0 := by
    linear_combination (h4-2*h2)/2
  have hL0C : (L:ℂ)^2≠0 := pow_ne_zero 2 (by exact_mod_cast hL0)
  have hzero := (mul_eq_zero.mp hd).resolve_left hL0C
  have hv := hpos _ (he k')
  rw [hzero] at hv
  simp at hv

/-- The value pairing `Σ conj(x_p) y_p` on a zero algebra with all multiplicities one. -/
def valuePairing {m : ι → ℕ} : ZeroAlgebra m →ₗ⋆[ℂ] ZeroAlgebra m →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => x.sum fun p c => starRingEnd ℂ c*y p)
    (fun x x' y => by
      rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])])
    (fun c x y => by
      rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
      simp [smul_eq_mul, mul_assoc])
    (fun x y y' => by
      simp only [Finsupp.add_apply, mul_add, Finsupp.sum_add])
    (fun c x y => by
      simp only [Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
      congr 1; funext p d; ring)

theorem valuePairing_apply {m : ι → ℕ} (x y : ZeroAlgebra m) :
    valuePairing x y=x.sum fun p c => starRingEnd ℂ c*y p := rfl

/-- **Existence.**  If every point is real and simple, the value pairing is a positive-definite
invariant form. -/
theorem exists_posDef_invariantForm {ρ : ι → ℂ} {m : ι → ℕ} (hreal : ∀ i, (ρ i).im=0)
    (hsimple : ∀ i, m i=1) :
    ∃ H : InvariantForm ρ m, ∀ x : ZeroAlgebra m, x≠0 → 0<(H.form x x).re := by
  have hunit : ∀ (i : ι) (a : ℝ),
      starRingEnd ℂ (Complex.exp (I*a*ρ i))*Complex.exp (I*a*ρ i)=1 := by
    intro i a
    rw [conj_exp_mul_exp]
    have : ρ i-starRingEnd ℂ (ρ i)=0 := by
      apply Complex.ext <;> simp [hreal i]
    rw [this, mul_zero, Complex.exp_zero]
  -- with simple points the action is diagonal: `(M_a x)_p = e^{iaρ} x_p`
  have hdiag : ∀ (a : ℝ) (x : ZeroAlgebra m) (p : JetIndex m),
      act ρ m a x p=Complex.exp (I*a*ρ p.1)*x p := by
    intro a x p
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp [hx, hy, mul_add]
    | single r c =>
      rw [show Finsupp.single r c=c • e r.1 r.2 by simp [e]]
      rw [map_smul, act_e_top ρ m a r.1 r.2 (by have := r.2.isLt; have := hsimple r.1; omega)]
      obtain ⟨i, k⟩ := r
      obtain ⟨p1, p2⟩ := p
      by_cases hip : (⟨i, k⟩ : JetIndex m)=⟨p1, p2⟩
      · rw [hip]; simp [e]; ring
      · simp [e, Finsupp.single_apply, hip]
  refine ⟨⟨valuePairing, ?_, ?_⟩, ?_⟩
  · intro x y
    rw [valuePairing_apply, valuePairing_apply, map_finsuppSum]
    simp only [map_mul, Complex.conj_conj]
    rw [Finsupp.sum, Finsupp.sum]
    sorry
  · sorry
  · sorry

end

end RHTower.ZeroAlgebraInvariantForms
