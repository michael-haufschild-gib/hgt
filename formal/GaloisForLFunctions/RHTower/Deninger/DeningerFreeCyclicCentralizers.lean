import GaloisForLFunctions.RHTower.Deninger.DeningerRootCyclicCentralizers
import GaloisForLFunctions.RHTower.Deninger.DeningerFreeGroupRoots
import GaloisForLFunctions.RHTower.Deninger.DeningerCycRecursion

/-!
# A free group has cyclic centralizers

A free group is an amalgam of infinite cyclic groups over the trivial group.  The base group being
trivial, the two hypotheses of the descent hold for free, so an element with a long cyclic reduction
has an infinite cyclic centralizer; an element conjugate into a factor has the factor itself as its
centralizer, the factors being infinite cyclic; and no element is conjugate to a nontrivial element
of the base group, there being none.

* `deningerFreePushout_cyclicCentralizers` : for the amalgam.
* `deningerFreeGroup_cyclicCentralizers` : for the free group.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- **Cyclic centralizers transport along an isomorphism.** -/
theorem deningerCyclicCentralizers_of_mulEquiv {G K : Type u} [Group G] [Group K] (e : G ≃* K)
    (h : DeningerCyclicCentralizers G) : DeningerCyclicCentralizers K := by
  intro x hx
  obtain ⟨y, hy, hC⟩ := h (e.symm x) (by
    intro hc
    exact hx (by rw [← e.apply_symm_apply x, hc, map_one]))
  refine ⟨e y, ?_, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · intro n hn
    refine hy n (e.injective ?_)
    rw [map_zpow, hn, map_one]
  · obtain ⟨k, hk'⟩ := (hC (e.symm z)).1 (by
      rw [← map_mul, ← map_inv, ← map_mul, hz])
    have hk : y ^ k = e.symm z := hk'
    refine ⟨k, ?_⟩
    show (e y) ^ k = z
    rw [← map_zpow, hk, e.apply_symm_apply]
  · obtain ⟨k, hk'⟩ := hz
    have hk : (e y) ^ k = z := hk'
    have hcom : (y ^ k) * (e.symm x) * (y ^ k)⁻¹ = e.symm x := (hC (y ^ k)).2 ⟨k, rfl⟩
    rw [← hk, ← map_zpow]
    refine e.symm.injective ?_
    rw [map_mul, map_mul, map_inv, e.symm_apply_apply]
    exact hcom

/-- The structure maps of a free group as an amalgam are injective, their domain being trivial. -/
theorem deningerFreeMap_injective (ι : Type u) :
    ∀ i, Function.Injective (deningerFreeMap ι i) := by
  intro i x y _
  exact Subsingleton.elim x y

/-- The generator of a factor of a free product. -/
noncomputable def deningerFreeGen (ι : Type u) (i : ι) : deningerFreeFactor ι i :=
  deningerRootGen.{u}

/-- **The centralizer of a nontrivial element of a factor** of a free product is the factor. -/
theorem deningerFreeOf_centralizer (ι : Type u) (i : ι) (u : deningerFreeFactor ι i)
    (hu : PushoutI.of (φ := deningerFreeMap ι) i u ≠ 1) :
    ∀ z : PushoutI (deningerFreeMap ι),
      z * (PushoutI.of (φ := deningerFreeMap ι) i u) * z⁻¹ =
        PushoutI.of (φ := deningerFreeMap ι) i u ↔
        z ∈ Subgroup.zpowers
          (PushoutI.of (φ := deningerFreeMap ι) i (deningerFreeGen ι i)) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerFreeMap ι)
    (deningerFreeMap_injective ι)
  have hune : u ≠ 1 := by
    intro hc
    exact hu (by rw [hc, map_one])
  have hurange : u ∉ (deningerFreeMap ι i).range := by
    rintro ⟨k, hk⟩
    exact hune (by rw [← hk]; rfl)
  intro z
  constructor
  · intro hz
    have hcomm : z * PushoutI.of (φ := deningerFreeMap ι) i u =
        PushoutI.of (φ := deningerFreeMap ι) i u * z := by
      calc z * PushoutI.of (φ := deningerFreeMap ι) i u
          = z * PushoutI.of (φ := deningerFreeMap ι) i u * z⁻¹ * z := by group
        _ = PushoutI.of (φ := deningerFreeMap ι) i u * z := by rw [hz]
    rcases deningerCentralizer_factor (d := d) i u hurange z hcomm with ⟨x, hx⟩ | ⟨x', k, hk⟩
    · refine ⟨Multiplicative.toAdd (MulEquiv.ulift x), ?_⟩
      show (PushoutI.of (φ := deningerFreeMap ι) i (deningerFreeGen ι i)) ^
        (Multiplicative.toAdd (MulEquiv.ulift x)) = z
      have hgen : (deningerFreeGen ι i) ^ (Multiplicative.toAdd (MulEquiv.ulift x)) = x :=
        deningerFreeFactor_zpow ι i x
      rw [← map_zpow, hgen, ← hx]
    · refine absurd ?_ hune
      have h1 : x'⁻¹ * u * x' = 1 := hk
      calc u = x' * (x'⁻¹ * u * x') * x'⁻¹ := by group
        _ = 1 := by rw [h1]; group
  · rintro ⟨c, hc'⟩
    have hc : (PushoutI.of (φ := deningerFreeMap ι) i (deningerFreeGen ι i)) ^ c = z := hc'
    have hab : ∀ x y : ULift.{u} (Multiplicative ℤ), x * y * x⁻¹ = y := by
      intro x y
      rw [mul_comm x y, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hc, ← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (PushoutI.of (φ := deningerFreeMap ι) i) (hab _ u)

/-- **The amalgam presenting a free group has cyclic centralizers.** -/
theorem deningerFreePushout_cyclicCentralizers (ι : Type u) [Nonempty ι] :
    DeningerCyclicCentralizers (PushoutI (deningerFreeMap ι)) := by
  classical
  have hφ := deningerFreeMap_injective ι
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerFreeMap ι) hφ
  have huniq : ∀ (x y : PushoutI (deningerFreeMap ι)) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y := by
    intro x y n hn h
    refine deningerUniqueRoots_of_mulEquiv (deningerFreeGroupEquiv ι) ?_ x y n hn h
    exact fun a b k hk hab => deningerFreeGroup_uniqueRoots ι a b k hk hab
  have hcent : ∀ (i : ι) (x : deningerFreeFactor ι i) (u v : PUnit.{u + 1}),
      x * deningerFreeMap ι i u * x⁻¹ = deningerFreeMap ι i v → v = u :=
    fun _ _ u v _ => Subsingleton.elim v u
  have hself : ∀ (i : ι) (x : deningerFreeFactor ι i) (v : PUnit.{u + 1}),
      i ≠ Classical.arbitrary ι → v ≠ 1 →
      x * deningerFreeMap ι i v * x⁻¹ = deningerFreeMap ι i v →
      x ∈ (deningerFreeMap ι i).range :=
    fun _ _ v _ hv _ => absurd (Subsingleton.elim v 1) hv
  intro w hw
  rcases deningerExists_letterProd (d := d) w with ⟨h₀, hw₀, -⟩ | ⟨L, hLne, hLred, hLalt, -, hw₀⟩
  · refine absurd ?_ hw
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 : deningerFreeMap ι i h₀ = 1 := rfl
    rw [hw₀, ← PushoutI.of_apply_eq_base (deningerFreeMap ι) i h₀, h1, map_one]
  · obtain ⟨C, R, V, hsplit, -, hVne, hVred, hValt, -, hprodR, hVcases⟩ :=
      deningerExists_cycData (φ := deningerFreeMap ι) L hLne hLred hLalt
    have hwconj : w = deningerLetterProd (φ := deningerFreeMap ι) C *
        deningerLetterProd (φ := deningerFreeMap ι) V *
        (deningerLetterProd (φ := deningerFreeMap ι) C)⁻¹ := by
      rw [hw₀, hsplit, deningerLetterProd_append, hprodR, ← mul_assoc]
    by_cases hV2 : 2 ≤ V.length
    · have hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1 := by
        rcases hVcases with hc | hc
        · omega
        · exact hc
      obtain ⟨y, hy, hC⟩ := deningerCycRedConj_centralizer (d := d) hcent (Classical.arbitrary ι)
        hself huniq V hV2 hVred hValt hVcyc (deningerLetterProd (φ := deningerFreeMap ι) C)
      exact ⟨deningerLetterProd (φ := deningerFreeMap ι) C * y *
        (deningerLetterProd (φ := deningerFreeMap ι) C)⁻¹,
        deningerConj_order y _ hy, by rw [hwconj]; exact hC⟩
    · have hVpos : 0 < V.length := List.length_pos_iff.2 hVne
      obtain ⟨q, hq⟩ : ∃ q, V = [q] := List.length_eq_one_iff.mp (by omega)
      have hqred : q.2 ∉ (deningerFreeMap ι q.1).range :=
        hVred q (by rw [hq]; exact List.mem_cons_self)
      have hVq : deningerLetterProd (φ := deningerFreeMap ι) V =
          PushoutI.of (φ := deningerFreeMap ι) q.1 q.2 := by
        rw [hq, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
      have hqne : PushoutI.of (φ := deningerFreeMap ι) q.1 q.2 ≠ 1 := by
        intro hc
        refine hqred ⟨1, ?_⟩
        refine PushoutI.of_injective hφ q.1 ?_
        rw [map_one, map_one]
        exact hc.symm
      obtain ⟨y, hy, hC⟩ := deningerCyclicCentralizer_conj
        (PushoutI.of (φ := deningerFreeMap ι) q.1 q.2)
        (deningerLetterProd (φ := deningerFreeMap ι) C)
        (PushoutI.of (φ := deningerFreeMap ι) q.1 (deningerFreeGen ι q.1))
        (by
          intro n hn
          have h2 : (deningerFreeGen ι q.1) ^ n = 1 := by
            refine PushoutI.of_injective hφ q.1 ?_
            rw [map_zpow, hn]
            exact (map_one (PushoutI.of (φ := deningerFreeMap ι) q.1)).symm
          exact deningerRootGen_order n h2)
        (deningerFreeOf_centralizer ι q.1 q.2 hqne)
      exact ⟨y, hy, by rw [hwconj, hVq]; exact hC⟩

/-- **A free group has cyclic centralizers.** -/
theorem deningerFreeGroup_cyclicCentralizers (ι : Type u) [Nonempty ι] :
    DeningerCyclicCentralizers (FreeGroup ι) :=
  deningerCyclicCentralizers_of_mulEquiv (deningerFreeGroupEquiv ι).symm
    (deningerFreePushout_cyclicCentralizers ι)

end RHTower
