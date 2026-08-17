import GaloisForLFunctions.HTGeometry.MilnorKTateFiltration
import GaloisForLFunctions.HTGeometry.RationalTameData

/-!
# Tate's Euclidean step

Modulo one level of the filtration, the symbol `{u, p}` of a `(p−1)`-smooth unit depends only on the
residue of `u` mod `p`.  The whole content is one application of the Steinberg relation:

with `0 < a, b < p`, write `a b = k p + c` with `0 < c < p` and `0 ≤ k < p`.  Then

```text
x := −k p / c ,   1 − x = (c + k p)/c = a b / c ,
0 = {x, 1 − x} = {−1, W} + {k, W} + {p, W} + {c⁻¹, W}        (W := a b / c)
```

and every term other than `{p, W}` is a symbol of `(p−1)`-smooth units.  Hence
`{a, p} + {b, p} − {c, p} = {W, p} = −{p, W}` lies one level down.

Iterating this over the generators shows that every `(p−1)`-smooth `u` has a representative
`0 < c < p` with `c ≡ res_p u` and `{u, p} − {c, p}` one level down.  When `res_p u = 1` the
representative is `1`, and `{u, p}` itself lies one level down — which is the descent step.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

instance factPrimeSubtype (i : {q : ℕ // q.Prime}) : Fact i.1.Prime := ⟨i.2⟩

section Euclid

variable {p : ℕ} [Fact p.Prime]

theorem nat_eq_of_zmod_cast_eq {m n : ℕ} (hm : m < p) (hn : n < p)
    (h : ((m : ZMod p)) = (n : ZMod p)) : m = n := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hc := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hm, ZMod.val_cast_of_lt hn] at hc

omit [Fact p.Prime] in
theorem natRatUnit_mem_smoothUnits_pred {m : ℕ} (hm : m ≠ 0) (hmp : m < p) :
    natRatUnit hm ∈ smoothUnits (p - 1) :=
  natRatUnit_mem_smoothUnits_of_lt hm (by omega)

theorem ratRes_natRatUnit {m : ℕ} (hm : m ≠ 0) :
    ratRes p ((natRatUnit hm : ℚˣ) : ℚ) = (m : ZMod p) := by
  rw [natRatUnit_val]
  exact ratRes_natCast m

theorem ratTameHom_milnorSym2 (a b : ℚˣ) :
    ratTameHom p (milnorSym2 ℚ a b) = Additive.ofMul ((ratTameData p).tame a b) :=
  ratTameHom_symbol a b

/-! ## The Euclidean relation -/

omit [Fact p.Prime] in
/-- **The Euclidean step.**  For `0 < a, b < p` the symbol relation
`{a, p} + {b, p} = {a b mod p, p}` holds modulo one level down. -/
theorem euclid_relation (hp : p.Prime) {a b : ℕ} (ha0 : a ≠ 0) (hap : a < p)
    (hb0 : b ≠ 0) (hbp : b < p) (hc0 : (a * b) % p ≠ 0) :
    milnorSym2 ℚ (natRatUnit ha0) (primeRatUnit hp)
        + milnorSym2 ℚ (natRatUnit hb0) (primeRatUnit hp)
        - milnorSym2 ℚ (natRatUnit hc0) (primeRatUnit hp) ∈ smoothK2 (p - 1) := by
  have hppos : 0 < p := hp.pos
  set c : ℕ := (a * b) % p with hcdef
  set k : ℕ := (a * b) / p with hkdef
  have hdm : p * k + c = a * b := Nat.div_add_mod (a * b) p
  have hcp : c < p := Nat.mod_lt _ hppos
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha0 hb0
  have hkp : k < p := by
    by_contra hcon
    have hcon' : p ≤ k := not_lt.mp hcon
    have h1 : p * p ≤ p * k := Nat.mul_le_mul_left p hcon'
    have h2 : a * b < p * p := by
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      nlinarith
    omega
  set P : ℚˣ := primeRatUnit hp with hP
  set A : ℚˣ := natRatUnit ha0 with hA
  set B : ℚˣ := natRatUnit hb0 with hB
  set C : ℚˣ := natRatUnit hc0 with hC
  have hAm : A ∈ smoothUnits (p - 1) := natRatUnit_mem_smoothUnits_pred ha0 hap
  have hBm : B ∈ smoothUnits (p - 1) := natRatUnit_mem_smoothUnits_pred hb0 hbp
  have hCm : C ∈ smoothUnits (p - 1) := natRatUnit_mem_smoothUnits_pred hc0 hcp
  have hnegm : (-1 : ℚˣ) ∈ smoothUnits (p - 1) := neg_one_mem_smoothUnits (p - 1)
  -- the target is the symbol of `W = a b / c`
  set W : ℚˣ := A * B * C⁻¹ with hW
  have hWm : W ∈ smoothUnits (p - 1) :=
    mul_mem (mul_mem hAm hBm) (inv_mem hCm)
  have hWsym : milnorSym2 ℚ W P
      = milnorSym2 ℚ A P + milnorSym2 ℚ B P - milnorSym2 ℚ C P := by
    rw [hW, milnorSym2_mul_left, milnorSym2_mul_left, milnorSym2_inv_left]
    abel
  rw [← hWsym]
  -- rational values
  have hcQ : ((c : ℚ)) ≠ 0 := by
    exact_mod_cast hc0
  have hWval : ((W : ℚˣ) : ℚ) = (a : ℚ) * (b : ℚ) / (c : ℚ) := by
    rw [hW, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, hA, hB, hC,
      natRatUnit_val, natRatUnit_val, natRatUnit_val]
    field_simp
  by_cases hk : k = 0
  · -- no carry: the relation is exact
    have hcab : c = a * b := by
      rw [hk, Nat.mul_zero, zero_add] at hdm
      exact hdm
    have hWone : W = 1 := by
      refine Units.ext ?_
      rw [hWval, Units.val_one, hcab]
      push_cast
      field_simp
    rw [hWone, milnorSym2_one_left]
    exact zero_mem _
  · set K : ℚˣ := natRatUnit hk with hK
    have hKm : K ∈ smoothUnits (p - 1) := natRatUnit_mem_smoothUnits_pred hk hkp
    set x : ℚˣ := (-1 : ℚˣ) * K * P * C⁻¹ with hx
    have hxval : ((x : ℚˣ) : ℚ) = -((k : ℚ) * (p : ℚ) / (c : ℚ)) := by
      rw [hx, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        hK, hC, natRatUnit_val, natRatUnit_val]
      have hneg : (((-1 : ℚˣ)) : ℚ) = -1 := by norm_num
      rw [hneg, hP, primeRatUnit_val]
      field_simp
    have hkQ : (0 : ℚ) < (k : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hppos
    have hcQpos : (0 : ℚ) < (c : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc0
    have hxne : ((x : ℚˣ) : ℚ) ≠ 1 := by
      rw [hxval]
      have : (0 : ℚ) < (k : ℚ) * (p : ℚ) / (c : ℚ) := by positivity
      intro hcon
      linarith
    -- `1 − x = W`
    have honeSub : oneSubUnit hxne = W := by
      refine Units.ext ?_
      rw [oneSubUnit_val, hxval, hWval]
      have hdmQ : (p : ℚ) * (k : ℚ) + (c : ℚ) = (a : ℚ) * (b : ℚ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hdm
      field_simp
      linarith [hdmQ]
    have hstein : milnorSym2 ℚ x (oneSubUnit hxne) = 0 := milnorSym2_steinberg hxne
    rw [honeSub] at hstein
    -- expand the left slot
    have hexp : milnorSym2 ℚ x W
        = milnorSym2 ℚ (-1 : ℚˣ) W + milnorSym2 ℚ K W + milnorSym2 ℚ P W
          + milnorSym2 ℚ C⁻¹ W := by
      rw [hx, milnorSym2_mul_left, milnorSym2_mul_left, milnorSym2_mul_left]
    rw [hexp] at hstein
    have hPW : milnorSym2 ℚ P W
        = -(milnorSym2 ℚ (-1 : ℚˣ) W + milnorSym2 ℚ K W + milnorSym2 ℚ C⁻¹ W) := by
      have h := hstein
      rw [← sub_eq_zero]
      rw [neg_add, neg_add]
      abel_nf
      abel_nf at h
      linear_combination (norm := abel) h
    have hmem : milnorSym2 ℚ P W ∈ smoothK2 (p - 1) := by
      rw [hPW]
      refine neg_mem (add_mem (add_mem ?_ ?_) ?_)
      · exact milnorSym2_mem_smoothK2 hnegm hWm
      · exact milnorSym2_mem_smoothK2 hKm hWm
      · exact milnorSym2_mem_smoothK2 (inv_mem hCm) hWm
    have hWP : milnorSym2 ℚ W P = -milnorSym2 ℚ P W := milnorSym2_antisymm W P
    rw [hWP]
    exact neg_mem hmem

/-! ## The representative subgroup -/

theorem natCast_ne_zero_of_lt {c : ℕ} (hc : c ≠ 0) (hcp : c < p) : ((c : ZMod p) ≠ 0) := by
  rw [Ne, natCast_zmod_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hdvd
  omega

/-- The `(p−1)`-smooth units that have a representative in `(0, p)` for the symbol against `p`. -/
def tateRepSet (hp : p.Prime) : Subgroup ℚˣ where
  carrier := {u : ℚˣ | ∃ c : ℕ, ∃ hc : c ≠ 0, c < p ∧
      ((c : ZMod p) = ratRes p ((u : ℚˣ) : ℚ)) ∧
      milnorSym2 ℚ u (primeRatUnit hp) - milnorSym2 ℚ (natRatUnit hc) (primeRatUnit hp)
        ∈ smoothK2 (p - 1)}
  one_mem' := by
    refine ⟨1, one_ne_zero, hp.one_lt, ?_, ?_⟩
    · rw [Units.val_one, ratRes_one]
      simp
    · have h1 : natRatUnit (one_ne_zero (α := ℕ)) = (1 : ℚˣ) := natRatUnit_one
      rw [h1, sub_self]
      exact zero_mem _
  mul_mem' := by
    rintro u1 u2 ⟨c1, hc1, hc1p, hr1, hs1⟩ ⟨c2, hc2, hc2p, hr2, hs2⟩
    have hn1 : ((c1 : ZMod p) ≠ 0) := natCast_ne_zero_of_lt hc1 hc1p
    have hn2 : ((c2 : ZMod p) ≠ 0) := natCast_ne_zero_of_lt hc2 hc2p
    have hd : ¬ p ∣ c1 * c2 := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
      · exact hn1 ((natCast_zmod_eq_zero_iff).2 h)
      · exact hn2 ((natCast_zmod_eq_zero_iff).2 h)
    have hc0 : (c1 * c2) % p ≠ 0 := by
      intro hcon
      exact hd (Nat.dvd_of_mod_eq_zero hcon)
    refine ⟨(c1 * c2) % p, hc0, Nat.mod_lt _ hp.pos, ?_, ?_⟩
    · have hcast : (((c1 * c2) % p : ℕ) : ZMod p) = ((c1 : ZMod p)) * (c2 : ZMod p) := by
        rw [ZMod.natCast_mod]
        push_cast
        ring
      have hu1 : IsPadicUnit p ((u1 : ℚˣ) : ℚ) :=
        isPadicUnit_of_ratRes_ne_zero (by rw [← hr1]; exact hn1)
      have hu2 : IsPadicUnit p ((u2 : ℚˣ) : ℚ) :=
        isPadicUnit_of_ratRes_ne_zero (by rw [← hr2]; exact hn2)
      rw [hcast, hr1, hr2, Units.val_mul, ratRes_mul hu1 hu2]
    · have heu := euclid_relation hp hc1 hc1p hc2 hc2p hc0
      have hsplit : milnorSym2 ℚ (u1 * u2) (primeRatUnit hp)
            - milnorSym2 ℚ (natRatUnit hc0) (primeRatUnit hp)
          = (milnorSym2 ℚ u1 (primeRatUnit hp)
                - milnorSym2 ℚ (natRatUnit hc1) (primeRatUnit hp))
            + (milnorSym2 ℚ u2 (primeRatUnit hp)
                - milnorSym2 ℚ (natRatUnit hc2) (primeRatUnit hp))
            + (milnorSym2 ℚ (natRatUnit hc1) (primeRatUnit hp)
                + milnorSym2 ℚ (natRatUnit hc2) (primeRatUnit hp)
                - milnorSym2 ℚ (natRatUnit hc0) (primeRatUnit hp)) := by
        rw [milnorSym2_mul_left]
        abel
      rw [hsplit]
      exact add_mem (add_mem hs1 hs2) heu
  inv_mem' := by
    rintro u ⟨c, hc, hcp, hr, hs⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hn : ((c : ZMod p) ≠ 0) := natCast_ne_zero_of_lt hc hcp
    set d : ZMod p := ((c : ZMod p))⁻¹ with hd
    have hdne : d ≠ 0 := inv_ne_zero hn
    set c' : ℕ := d.val with hc'
    have hc'p : c' < p := ZMod.val_lt d
    have hcast' : ((c' : ℕ) : ZMod p) = d := ZMod.natCast_rightInverse d
    have hc'0 : c' ≠ 0 := by
      intro hcon
      refine hdne ?_
      rw [← hcast', hcon]
      simp
    -- the product is one
    have hprod : ((c * c' : ℕ) : ZMod p) = 1 := by
      push_cast
      rw [hcast', hd]
      exact mul_inv_cancel₀ hn
    have hmod : (c * c') % p = 1 := by
      refine nat_eq_of_zmod_cast_eq (Nat.mod_lt _ hp.pos) hp.one_lt ?_
      rw [ZMod.natCast_mod, hprod]
      simp
    have hmod0 : (c * c') % p ≠ 0 := by
      rw [hmod]
      exact one_ne_zero
    have heu := euclid_relation hp hc hcp hc'0 hc'p hmod0
    have hone : natRatUnit hmod0 = (1 : ℚˣ) := by
      have : natRatUnit hmod0 = natRatUnit (by rw [hmod]; exact one_ne_zero : (c * c') % p ≠ 0) :=
        rfl
      refine Units.ext ?_
      rw [natRatUnit_val, hmod]
      norm_num
    rw [hone, milnorSym2_one_left, sub_zero] at heu
    refine ⟨c', hc'0, hc'p, ?_, ?_⟩
    · have hu : IsPadicUnit p ((u : ℚˣ) : ℚ) :=
        isPadicUnit_of_ratRes_ne_zero (by rw [← hr]; exact hn)
      rw [hcast', hd, hr, Units.val_inv_eq_inv_val, ratRes_inv hu]
    · have hsplit : milnorSym2 ℚ u⁻¹ (primeRatUnit hp)
            - milnorSym2 ℚ (natRatUnit hc'0) (primeRatUnit hp)
          = -(milnorSym2 ℚ u (primeRatUnit hp)
                - milnorSym2 ℚ (natRatUnit hc) (primeRatUnit hp))
            - (milnorSym2 ℚ (natRatUnit hc) (primeRatUnit hp)
                + milnorSym2 ℚ (natRatUnit hc'0) (primeRatUnit hp)) := by
        rw [milnorSym2_inv_left]
        abel
      rw [hsplit]
      exact sub_mem (neg_mem hs) heu

/-- **Every `(p−1)`-smooth unit has a representative.** -/
theorem exists_tateRep (hp : p.Prime) {u : ℚˣ} (hu : u ∈ smoothUnits (p - 1)) :
    ∃ c : ℕ, ∃ hc : c ≠ 0, c < p ∧ ((c : ZMod p) = ratRes p ((u : ℚˣ) : ℚ)) ∧
      milnorSym2 ℚ u (primeRatUnit hp) - milnorSym2 ℚ (natRatUnit hc) (primeRatUnit hp)
        ∈ smoothK2 (p - 1) := by
  have hle : smoothUnits (p - 1) ≤ tateRepSet hp := by
    refine le_trans (smoothUnits_le_closure (p - 1)) ((Subgroup.closure_le _).2 ?_)
    rintro v (hv | ⟨q, hq, hqN, rfl⟩)
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      refine ⟨p - 1, ?_, ?_, ?_, ?_⟩
      · have := hp.two_le
        omega
      · have := hp.two_le
        omega
      · have hval : (((-1 : ℚˣ)) : ℚ) = ((-1 : ℤ) : ℚ) := by norm_num
        rw [hval, ratRes_intCast]
        have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
        have hpz : ((p : ℕ) : ZMod p) = 0 := by
          have := (natCast_zmod_eq_zero_iff (p := p) (n := p)).2 dvd_rfl
          exact this
        have hsub : ((p - 1 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) - ((1 : ℕ) : ZMod p) :=
          Nat.cast_sub h1
        rw [hsub, hpz, Nat.cast_one, zero_sub]
        push_cast
        ring
      · -- {−1, p} = {p−1, p}
        have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
        have hPval : ((primeRatUnit hp : ℚˣ) : ℚ) = (p : ℚ) := primeRatUnit_val hp
        have hne : ((primeRatUnit hp : ℚˣ) : ℚ) ≠ 1 := by
          rw [hPval]
          have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
          intro hcon
          rw [hcon] at this
          norm_num at this
        have hst : milnorSym2 ℚ (primeRatUnit hp) (oneSubUnit hne) = 0 :=
          milnorSym2_steinberg hne
        have hval1 : ((oneSubUnit hne : ℚˣ) : ℚ) = 1 - (p : ℚ) := by
          rw [oneSubUnit_val, hPval]
        have hfac : oneSubUnit hne = (-1 : ℚˣ) * natRatUnit hp1 := by
          refine Units.ext ?_
          rw [hval1, Units.val_mul, natRatUnit_val]
          have hneg : (((-1 : ℚˣ)) : ℚ) = -1 := by norm_num
          rw [hneg]
          have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
          have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
            rw [Nat.cast_sub h1, Nat.cast_one]
          rw [hcast]
          ring
        rw [hfac, milnorSym2_mul_right] at hst
        have hanti1 : milnorSym2 ℚ (primeRatUnit hp) (-1 : ℚˣ)
            = -milnorSym2 ℚ (-1 : ℚˣ) (primeRatUnit hp) :=
          milnorSym2_antisymm _ _
        have hanti2 : milnorSym2 ℚ (primeRatUnit hp) (natRatUnit hp1)
            = -milnorSym2 ℚ (natRatUnit hp1) (primeRatUnit hp) :=
          milnorSym2_antisymm _ _
        rw [hanti1, hanti2] at hst
        have htors : milnorSym2 ℚ (-1 : ℚˣ) (primeRatUnit hp)
            + milnorSym2 ℚ (-1 : ℚˣ) (primeRatUnit hp) = 0 := by
          rw [← milnorSym2_mul_left]
          have : ((-1 : ℚˣ)) * (-1 : ℚˣ) = 1 := by
            refine Units.ext ?_
            norm_num
          rw [this, milnorSym2_one_left]
        have hzero : milnorSym2 ℚ (-1 : ℚˣ) (primeRatUnit hp)
            - milnorSym2 ℚ (natRatUnit hp1) (primeRatUnit hp) = 0 := by
          have h1 : milnorSym2 ℚ (-1 : ℚˣ) (primeRatUnit hp)
              + milnorSym2 ℚ (natRatUnit hp1) (primeRatUnit hp) = 0 := by
            have := hst
            linear_combination (norm := abel) -this
          linear_combination (norm := abel) htors - h1
        rw [hzero]
        exact zero_mem _
    · refine ⟨q, hq.ne_zero, ?_, ?_, ?_⟩
      · have := hp.two_le
        omega
      · rw [ratRes_natRatUnit]
      · rw [sub_self]
        exact zero_mem _
  exact hle hu

/-! ## The descent -/

theorem mem_val_ker_of_mem_smoothUnits_pred (hp : p.Prime) {u : ℚˣ}
    (hu : u ∈ smoothUnits (p - 1)) : u ∈ (ratTameData p).val.ker := by
  have h2 := hp.two_le
  show u ∈ (ratPadicValHom p).ker
  rw [mem_ratPadicValHom_ker_iff]
  exact hu p hp (by omega)

theorem ratTameHom_eq_zero_of_mem_smoothK2_pred (hp : p.Prime) {y : MilnorKDeg ℚ 2}
    (hy : y ∈ smoothK2 (p - 1)) : ratTameHom p y = 0 := by
  have hle : smoothK2 (p - 1) ≤ (ratTameHom p).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, b, hb, rfl⟩
    show ratTameHom p (milnorSym2 ℚ a b) = 0
    rw [ratTameHom_milnorSym2,
      (ratTameData p).tame_eq_one_of_mem_ker (mem_val_ker_of_mem_smoothUnits_pred hp ha)
        (mem_val_ker_of_mem_smoothUnits_pred hp hb)]
    rfl
  exact hle hy

theorem ratRes_eq_one_of_tame_symbol_eq_zero (hp : p.Prime) {u : ℚˣ}
    (hu : u ∈ smoothUnits (p - 1))
    (h : ratTameHom p (milnorSym2 ℚ u (primeRatUnit hp)) = 0) :
    ratRes p ((u : ℚˣ) : ℚ) = 1 := by
  have hker := mem_val_ker_of_mem_smoothUnits_pred hp hu
  rw [ratTameHom_milnorSym2] at h
  have hv : (ratTameData p).v (primeRatUnit hp) = 1 := by
    show padicValRat p ((primeRatUnit hp : ℚˣ) : ℚ) = 1
    rw [primeRatUnit_val]
    exact padicValRat_self_prime
  rw [(ratTameData p).tame_of_mem_ker_left hker, hv, zpow_one] at h
  have h1 : (ratTameData p).res ⟨u, hker⟩ = 1 := by
    have hc := congrArg Additive.toMul h
    simpa using hc
  have h3 : (((ratTameData p).res ⟨u, hker⟩ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [h1]
    rfl
  rw [← ratResHom_val hker]
  exact h3

/-- **The descent step at a prime.** -/
theorem smoothK2_descent_prime (hp : p.Prime) {x : MilnorKDeg ℚ 2} (hx : x ∈ smoothK2 p)
    (h0 : ratTameHom p x = 0) : x ∈ smoothK2 (p - 1) := by
  obtain ⟨y, hy, u, hu, rfl⟩ := smoothK2_le_tateDecomp hp hx
  have hy0 : ratTameHom p y = 0 := ratTameHom_eq_zero_of_mem_smoothK2_pred hp hy
  have hs0 : ratTameHom p (milnorSym2 ℚ u (primeRatUnit hp)) = 0 := by
    rw [map_add, hy0, zero_add] at h0
    exact h0
  have hres := ratRes_eq_one_of_tame_symbol_eq_zero hp hu hs0
  obtain ⟨c, hc, hcp, hrc, hsc⟩ := exists_tateRep hp hu
  have hc1 : c = 1 := by
    refine nat_eq_of_zmod_cast_eq hcp hp.one_lt ?_
    rw [hrc, hres]
    simp
  have hone : natRatUnit hc = (1 : ℚˣ) := by
    refine Units.ext ?_
    rw [natRatUnit_val, hc1]
    norm_num
  rw [hone, milnorSym2_one_left, sub_zero] at hsc
  exact add_mem hy hsc

end Euclid

section TateMain

/-- The tame data of `ℚ` at all primes, with residue fields `ZMod p`. -/
def ratTameFamily : ∀ i : {q : ℕ // q.Prime}, TameData ℚ (ZMod i.1) :=
  fun i => ratTameData i.1

/-- **A class with vanishing tame symbols descends to the bottom of the filtration.** -/
theorem mem_smoothK2_one_of_tame_vanishing {x : MilnorKDeg ℚ 2}
    (htame : ∀ i : {q : ℕ // q.Prime}, ratTameHom i.1 x = 0) :
    ∀ N : ℕ, x ∈ smoothK2 N → x ∈ smoothK2 1 := by
  intro N
  induction N with
  | zero => intro h; exact smoothK2_mono (Nat.zero_le 1) h
  | succ M ih =>
    intro h
    by_cases hpr : (M + 1).Prime
    · haveI : Fact (M + 1).Prime := ⟨hpr⟩
      have h' : x ∈ smoothK2 ((M + 1) - 1) :=
        smoothK2_descent_prime hpr h (htame ⟨M + 1, hpr⟩)
      have hidx : (M + 1) - 1 = M := rfl
      rw [hidx] at h'
      exact ih h'
    · rw [smoothK2_succ_of_not_prime hpr] at h
      exact ih h

/-- **Tate's theorem: the tame kernel of `ℚ` is killed by `2`.** -/
theorem two_zsmul_eq_zero_of_mem_ratTameKernel {y : MilnorKDeg ℚ 2}
    (hy : y ∈ tameKernel ratTameFamily) : (2 : ℤ) • y = 0 := by
  obtain ⟨N, hN⟩ := exists_mem_smoothK2 y
  have htame : ∀ i : {q : ℕ // q.Prime}, ratTameHom i.1 y = 0 := by
    intro i
    exact (mem_tameKernel_iff ratTameFamily y).1 hy i
  exact two_zsmul_eq_zero_of_mem_smoothK2_one (mem_smoothK2_one_of_tame_vanishing htame N hN)

theorem ratTameKernel_torsion (y : MilnorKDeg ℚ 2) (hy : y ∈ tameKernel ratTameFamily) :
    y ∈ torsionAddSubgroup (MilnorKDeg ℚ 2) :=
  ⟨2, two_ne_zero, two_zsmul_eq_zero_of_mem_ratTameKernel hy⟩

theorem finite_ratTameHom_ne_zero_symbol (a b : ℚˣ) :
    {i : {q : ℕ // q.Prime} |
      (ratTameFamily i).tameHom (milnorClassDeg ℚ 2 ⟨[a, b], rfl⟩) ≠ 0}.Finite := by
  obtain ⟨M, hM⟩ := exists_mem_smoothUnits a
  obtain ⟨N, hN⟩ := exists_mem_smoothUnits b
  set B : ℕ := max M N with hB
  have hsub : {i : {q : ℕ // q.Prime} |
      (ratTameFamily i).tameHom (milnorClassDeg ℚ 2 ⟨[a, b], rfl⟩) ≠ 0}
      ⊆ (Subtype.val ⁻¹' (Set.Iic B)) := by
    intro i hi
    by_contra hcon
    refine hi ?_
    have hlt : B < i.1 := by
      simpa [Set.mem_preimage, Set.mem_Iic] using hcon
    haveI : Fact i.1.Prime := ⟨i.2⟩
    have hav : a ∈ (ratTameData i.1).val.ker := by
      show a ∈ (ratPadicValHom i.1).ker
      rw [mem_ratPadicValHom_ker_iff]
      exact hM i.1 i.2 (lt_of_le_of_lt (le_max_left M N) hlt)
    have hbv : b ∈ (ratTameData i.1).val.ker := by
      show b ∈ (ratPadicValHom i.1).ker
      rw [mem_ratPadicValHom_ker_iff]
      exact hN i.1 i.2 (lt_of_le_of_lt (le_max_right M N) hlt)
    show (ratTameData i.1).tameHom (milnorClassDeg ℚ 2 ⟨[a, b], rfl⟩) = 0
    rw [(ratTameData i.1).tameHom_symbol,
      (ratTameData i.1).tame_eq_one_of_mem_ker hav hbv]
    rfl
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iic B)

/-- **The degree-two Milnor `K`-group of `ℚ` is torsion.** -/
theorem milnorKDegTwo_rat_torsion (x : MilnorKDeg ℚ 2) :
    x ∈ torsionAddSubgroup (MilnorKDeg ℚ 2) :=
  milnorKDegTwo_torsion_of_tameKernel_torsion ratTameFamily
    (tame_finiteSupport_of_symbols ratTameFamily finite_ratTameHom_ne_zero_symbol)
    ratTameKernel_torsion x

end TateMain

end

end GaloisForLFunctions.HTGeometry
