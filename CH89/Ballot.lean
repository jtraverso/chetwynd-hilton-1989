/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.List.Basic

/-!
# Ballot pairings

`exists_ballot_pairing`: let `ℓ` be a list without repetitions containing the disjoint sets `X`, `Y`
of equal size. If every prefix of `ℓ` has at most one more element of `Y` than of `X`, there is a
bijection `σ : Y → X` such that `σ y` comes before `y` in `ℓ` for all `y` but at most one
(Hall's theorem, with one dummy partner).
-/

@[expose] public section

namespace CH89

open Finset

variable {V : Type*} [DecidableEq V]

/-- Counting the members of `S` among the first `k` entries of a list without repetitions. -/
theorem card_filter_idxOf_lt {ℓ : List V} (hnd : ℓ.Nodup) {S : Finset V} (hS : ∀ v ∈ S, v ∈ ℓ)
    (k : ℕ) : #(S.filter fun v => ℓ.idxOf v < k) = ((ℓ.take k).filter (· ∈ S)).length := by
  have hnd' : ((ℓ.take k).filter (· ∈ S)).Nodup := (hnd.sublist (List.take_sublist _ _)).filter _
  rw [← List.toFinset_card_of_nodup hnd']
  congr 1
  ext v
  simp only [mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, hlt⟩
    exact ⟨(List.mem_take_iff_idxOf_lt (hS v hv)).2 hlt, hv⟩
  · rintro ⟨hv, hvS⟩
    exact ⟨hvS, (List.mem_take_iff_idxOf_lt (hS v hvS)).1 hv⟩

/-- **Ballot pairing.** -/
theorem exists_ballot_pairing {X Y : Finset V} (ℓ : List V) (hnd : ℓ.Nodup)
    (hXℓ : ∀ x ∈ X, x ∈ ℓ) (hYℓ : ∀ y ∈ Y, y ∈ ℓ) (hXY : Disjoint X Y) (hcard : #X = #Y)
    (z₀ : V) (hz₀ : z₀ ∉ X)
    (hpre : ∀ k, ((ℓ.take k).filter (· ∈ Y)).length ≤ ((ℓ.take k).filter (· ∈ X)).length + 1) :
    ∃ (σ : V → V) (Bad : Finset V), Bad ⊆ Y ∧ #Bad ≤ 1 ∧ (∀ y ∈ Y, σ y ∈ X) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, σ y = σ y' → y = y') ∧
      ∀ y ∈ Y, y ∉ Bad → ℓ.idxOf (σ y) < ℓ.idxOf y := by
  classical
  let t : Y → Finset V := fun y => insert z₀ (X.filter fun x => ℓ.idxOf x < ℓ.idxOf (y : V))
  have hall : ∀ s : Finset Y, #s ≤ #(s.biUnion t) := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    obtain ⟨y, hy, hmax⟩ := s.exists_max_image (fun y : Y => ℓ.idxOf (y : V)) hs
    have h1 : #(t y) ≤ #(s.biUnion t) := card_le_card (subset_biUnion_of_mem t hy)
    have h2 : #(t y) = #(X.filter fun x => ℓ.idxOf x < ℓ.idxOf (y : V)) + 1 :=
      card_insert_of_notMem (fun h => hz₀ (mem_filter.1 h).1)
    have h3 : #s ≤ #(Y.filter fun v => ℓ.idxOf v < ℓ.idxOf (y : V) + 1) := by
      refine card_le_card_of_injOn Subtype.val (fun a ha => ?_) Subtype.val_injective.injOn
      exact mem_filter.2 ⟨a.2, Nat.lt_succ_of_le (hmax a ha)⟩
    have h4 : (X.filter fun x => ℓ.idxOf x < ℓ.idxOf (y : V) + 1) =
        X.filter fun x => ℓ.idxOf x < ℓ.idxOf (y : V) := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨hx, hlt⟩
        refine ⟨hx, lt_of_le_of_ne (Nat.le_of_lt_succ hlt) fun e => ?_⟩
        have hxy : x = (y : V) := (List.idxOf_inj (hXℓ x hx)).1 e
        exact Finset.disjoint_left.1 hXY hx (by rw [hxy]; exact y.2)
      · rintro ⟨hx, hlt⟩; exact ⟨hx, Nat.lt_succ_of_lt hlt⟩
    have h5 := hpre (ℓ.idxOf (y : V) + 1)
    rw [← card_filter_idxOf_lt hnd hYℓ, ← card_filter_idxOf_lt hnd hXℓ, h4] at h5
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  -- the bad vertices
  let Bad : Finset V := Y.filter fun y => ∃ h : y ∈ Y, f ⟨y, h⟩ = z₀
  have hBadY : Bad ⊆ Y := filter_subset _ _
  have hBad1 : #Bad ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    obtain ⟨-, ha', hfa⟩ := mem_filter.1 ha
    obtain ⟨-, hb', hfb⟩ := mem_filter.1 hb
    have := hfinj (hfa.trans hfb.symm)
    exact congrArg Subtype.val this
  have hgood : ∀ y (h : y ∈ Y), y ∉ Bad → f ⟨y, h⟩ ∈ X ∧ ℓ.idxOf (f ⟨y, h⟩) < ℓ.idxOf y := by
    intro y h hb
    have hne : f ⟨y, h⟩ ≠ z₀ := fun e => hb (mem_filter.2 ⟨h, h, e⟩)
    have := hft ⟨y, h⟩
    rcases mem_insert.1 this with e | hx
    · exact absurd e hne
    · exact (mem_filter.1 hx)
  -- the image of the good vertices
  let g : V → V := fun y => if h : y ∈ Y then f ⟨y, h⟩ else z₀
  have hg : ∀ y (h : y ∈ Y), g y = f ⟨y, h⟩ := fun y h => by simp only [g, dif_pos h]
  let Img := (Y \ Bad).image g
  have hImgX : Img ⊆ X := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    obtain ⟨hyY, hyB⟩ := mem_sdiff.1 hy
    rw [hg y hyY]; exact (hgood y hyY hyB).1
  have hginj : Set.InjOn g (Y \ Bad : Finset V) := by
    intro a ha b hb e
    have ha' := (mem_sdiff.1 ha).1
    have hb' := (mem_sdiff.1 hb).1
    rw [hg a ha', hg b hb'] at e
    exact congrArg Subtype.val (hfinj e)
  have hImgc : #Img = #Y - #Bad := by
    rw [card_image_of_injOn hginj, card_sdiff_of_subset hBadY]
  obtain ⟨xe, hxe⟩ : ∃ xe, Bad.Nonempty → xe ∈ X ∧ xe ∉ Img := by
    by_cases hB : Bad.Nonempty
    · have hlt : #Img < #X := by
        have := card_pos.2 hB
        have := card_le_card hBadY
        omega
      obtain ⟨x, hx, hxI⟩ := exists_mem_notMem_of_card_lt_card hlt
      exact ⟨x, fun _ => ⟨hx, hxI⟩⟩
    · exact ⟨z₀, fun h => absurd h hB⟩
  let σ : V → V := fun y => if y ∈ Bad then xe else g y
  refine ⟨σ, Bad, hBadY, hBad1, fun y hy => ?_, fun y hy y' hy' e => ?_, fun y hy hb => ?_⟩
  · by_cases hb : y ∈ Bad
    · simp only [σ, if_pos hb]; exact (hxe ⟨y, hb⟩).1
    · simp only [σ, if_neg hb]; exact hImgX (mem_image.2 ⟨y, mem_sdiff.2 ⟨hy, hb⟩, rfl⟩)
  · by_cases hb : y ∈ Bad <;> by_cases hb' : y' ∈ Bad
    · exact card_le_one.1 hBad1 y hb y' hb'
    · simp only [σ, if_pos hb, if_neg hb'] at e
      exact absurd (e ▸ mem_image.2 ⟨y', mem_sdiff.2 ⟨hy', hb'⟩, rfl⟩) (hxe ⟨y, hb⟩).2
    · simp only [σ, if_neg hb, if_pos hb'] at e
      exact absurd (e.symm ▸ mem_image.2 ⟨y, mem_sdiff.2 ⟨hy, hb⟩, rfl⟩) (hxe ⟨y', hb'⟩).2
    · simp only [σ, if_neg hb, if_neg hb'] at e
      exact hginj (mem_sdiff.2 ⟨hy, hb⟩) (mem_sdiff.2 ⟨hy', hb'⟩) e
  · simp only [σ, if_neg hb, hg y hy]
    exact (hgood y hy hb).2

end CH89
