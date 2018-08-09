---
title: Monads from adjunctions, adjunctions from monads.
---

$$\newcommand{cat}{\mathsf}%
\newcommand{id}{\mathrm{id}}%
\newcommand{bind}{\mathbin{\mathrm{\gg=}}}%
\newcommand{hom}{\mathrm{hom}}%
\newcommand{natto}{\Rightarrow}%{\stackrel{\bullet}{\to}}%
\newcommand{Id}{\mathrm{Id}}%
$$

There is a tight relationship between monads and adjunctions. In fact,
it is easy to see that every pair of adjoint functors yields a
monad. What is really interesting is that conversely, every monad
arises by some adjunction.

Let's look at an example first. Fix a set $S$, then there is a natural
bijection of hom-sets in the category $\cat{Set}$:

$$c: \hom(X\times S, Y)\xrightarrow{\cong}\hom(X, \hom(S, Y))$$

otherwise known as "currying", taking a function $f : X\times S\to Y$
to a function $c(f) : X\to \hom(S, Y)$ defined by $c(f)(x) = s\mapsto
f(x,s)$. This can be interpreted as an adjunction, where $-\times S$
is the left adjoint to $\hom(S, -)$. The composition of these functors
is the functor $X\mapsto \hom(S, X\times S)$, which you might
recognize as the `State` monad. In fact, every adjunction yields a
monad.

# Adjoint functors

We recall the definition of an adjoint pair of functors and some
properties (without proof.) Let $C$, $D$ be categories, $F: C\to D$
and $G: D\to C$ be a pair of functors. Then $F$, $G$ is called an
*adjoint pair* if there is a natural bijection

$$\Phi_{XY} : \hom_D(FX, Y)\xrightarrow{\cong}\hom_C(X, GY).$$

We call $F$ the *left-adjoint* and $G$ the *right-adjoint*, and we
write $F\dashv G$.

An adjunction comes with natural transformations, $\eta: GF\natto\Id$,
the *unit* of the adjunction, and $\varepsilon : \Id\natto FG$, the
*counit*. These arise as follows:

$$\eta_X = \Phi_{X,FX}(\id_{FX}) : X\to GFX,$$

$$\varepsilon_Y = \Phi_{GY,Y}^{-1}(\id_{GY}) : FGY\to Y,$$

and they satisy so-called triangle equalities given by the following
commuting diagrams:

$$\require{AMScd}
\begin{CD}
F\circ\Id_C @>{F\bullet\eta}>> F\circ G\circ F\\
@| @V{\varepsilon\bullet F}VV\\
F @= \Id_D\circ F
\end{CD}$$

$$\begin{CD}
\Id_C\circ G @>{\eta\bullet G}>> G\circ F\circ G\\
@| @V{G\bullet \varepsilon}VV\\
G @= G\circ \Id_D
\end{CD}$$

(Forgive me if these don't show up as actual triangles due to
technical limitations.)

With these, we can write $\Phi$ in terms of $\eta$ and
$\varepsilon$:

$$\begin{align*}
\Phi_{XY}(f : FX\to Y) &= G(f)\circ\eta_X &: X \xrightarrow{\eta_X} GFX \xrightarrow{Gf} GY\\
\Phi^{-1}_{XY}(g :X\to GY) &= \varepsilon_Y\circ F(g) &: FX \xrightarrow{Fg} FGY \xrightarrow{\varepsilon_Y} Y
\end{align*}$$

This will come in handy later.

# Monads from adjunctions

If we post-compose the first triangle diagram with $G$ and pre-compose
the second with $F$, we obtain a very familiar diagram:

$$\begin{CD}
\Id_C\circ GF @>{\eta\bullet GF}>> GFGF @<{GF\bullet\eta}<< GF\circ\Id_C\\
@| @V{G\bullet\varepsilon\bullet F}VV @|\\
GF @= GF @= GF
\end{CD}$$

Setting $M := G\circ F$ and $\mu := G\bullet\varepsilon\bullet F$
results in the diagram for the left and right identities for monads
(where $\eta$ is the same.) To see that associativity holds, first
recall the horizontal composition $\varepsilon\bullet\varepsilon :
FGFG\natto\Id_D$. It was defined as the diagonal of this commuting
diagram:

$$\begin{CD}
FGFG @>{FG\bullet\varepsilon}>> FG\circ\Id_D\\
@V{\varepsilon\bullet FG}VV  @V{\varepsilon\bullet\Id_D}VV\\
\Id_D\circ FG @>{\Id_D\bullet\varepsilon}>> \Id_D\circ\Id_D
\end{CD}$$

Post-compose with $G$ and pre-compose with $F$, similar to what we did before:

$$\begin{CD}
GFGFGF    @>{GFG\bullet\varepsilon\bullet F}>>                GFGF\\
@V{G\bullet\varepsilon\bullet FGF}VV         @V{G\bullet\varepsilon \bullet F}VV\\
GFGF      @>{G\bullet\varepsilon\bullet F}>>                   GF
\end{CD}
\quad
\sim
\quad
\begin{CD}MMM     @>{M\bullet\mu}>>        MM\\
@V{\mu\bullet M}VV                        @V{\mu}VV\\
MM                     @>{\mu}>>            M
\end{CD}$$

This is exactly the associativity diagram we need.

Conclusion so far: Every adjunction yields a monad.

There's a dual statement included that I won't go into in this
article. Every adjunction also yields a comonad $W = F\circ G$, with the
given $\varepsilon: \Id\natto W$ and $\Delta = F\bullet\eta\bullet G :
W\natto WW$.

Let's see about the converse statement. Does every monad come from an
adjunction? 

# Adjunctions from monads

There are two very different _canonical_ ways to find an adjoint pair
that form a monad. In the following, let $(M,\eta,\mu)$ be a monad in
a category $C$.

## The Kleisli category

Let $C_M$ be the category whose objects are exactly the objects of
$C$, and whose arrows from $a$ to $b$ are exactly the $C$-morphisms
$a\to M(b)$. To avoid confusion, we're going to write $a\to_M b$ for
the arrows in $C_M$ and $a\to b$ for arrows in $C$. This way, an arrow
$a\to M(b)$ is the same as an arrow $a\to_M b$.

Given arrows $f: a\to M(b)$, $g: b\to M(c)$, an arrow $g\circ_M f:
a\to M(c)$ is given by the *Kleisli composition*, $g\circ_M f :=
\mu_c\circ M(g)\circ f$.

$$ g\circ_M f := a\stackrel{f}\longrightarrow
M(b)\stackrel{M(g)}{\longrightarrow} MM(c)\stackrel{\mu_c}{\to} M(c)$$

We check that this gives us a valid composition.

1. $\eta_b\circ_M f = \mu_b\circ M(\eta_b)\circ f = f$, because
$\mu\circ(M\bullet\eta) = \id_M$ (this is the _right_ identity law for
monads.)

2. $f\circ_M\eta_a = \mu_b\circ M(f)\circ\eta_a =
\mu_b\circ\eta_{Mb}\circ f = f$ by naturality and because
$\mu\circ(\eta\bullet M) =\id_M$ (this is the _left_ identity law.)

3. Let $h:c\to_M d$ be another arrow. Then

$$\begin{align*}
h\circ_M(g\circ_M f) &= h\circ_M(\mu_c\circ M(g)\circ f)\\
&= \mu_d\circ \underline{M(h) \circ \mu_c}\circ M(g)\circ f\\
&= \underline{\mu_d\circ\mu_{Md}}\circ MM(h)\circ M(g)\circ f\\
&= \mu_d\circ M(\mu_d)\circ MM(h)\circ M(g)\circ f\\
&= \mu_d\circ M(\mu_d\circ M(h)\circ g)\circ f\\
&= (h\circ_M g)\circ_M f,\end{align*}$$

by naturality and the associative law of monads.

We see that, indeed, $C_M$ is a category, where the composition is
given by $\circ_M$, and the identity associated with an object $a$ is
$\eta_a$. This category is called the *Kleisli category* of $M$.

Notation: The Kleisli composition is often written an operator like
`<=<`, there's a flipped form `>=>` called the "Kleisli fish".

## The Kleisli adjunction

Let's introduce two functors, $F: C\to C_M$ and $G: C_M\to C$. On
objects, $F$ maps each object to itself (remember that the objects of
$C_M$ are precisely the objects of $C$). On morphisms then, $F$ must map
$f: a\to b$ to $F(f) : a\to_M b$, that is, a morphism $a\to M(b)$. We
can accomplish that by post-composing with an $\eta$, so we have $F(f)
:= \eta_b \circ f: a\to M(b)$.

$f:a\to b\quad\leadsto\quad F(f): a\xrightarrow{f} b\xrightarrow{\eta_b} M(b)$

The other functor, $G$, can't just go back, because there's no general
way to obtain a morphism $a\to b$ from $a\to M(b)$. We cannot "unpack"
monads, but we can "flatten". So we define $G(a) = M(a)$ on objects,
and $G(f:a\to M(b)) = \mu_b \circ M(f)$.

$f: a\to M(b)\quad\leadsto\quad G(f): M(a)\xrightarrow{M(f)}
MM(b)\xrightarrow{\mu_b} M(b)$.

To show that they are adjoint, observe that a $C$-morphism $f: a\to
M(b)$ is simultaneously a morphism $a\to_M b$ in $C_M$, so with our
functors, it's $F(a)\to_M b$ and $a\to G(b)$ at the same time. This
means that the hom-set bijection is actually an identity.

$$\begin{align*}
\Phi_{ab} : \hom_{C_M}(Fa, b) &\xrightarrow{\cong} \hom_C(a, Gb)\\
f&\mapsto f
\end{align*}$$

What could be more natural than an identity? But not so fast, let's do
this carefully. To show that $\Phi_{ab}$ is natural, we have to show
that both composition rules "make sense". First, let $f: c\to a$ be a
morphism in $C$. Then $\hom_{C_M}(Ff, b)$ is precomposition with $Ff$,
that is, for $\varphi \in\hom_{C_M}(Fa, b)$, we have $\hom_{C_M}(Ff,
b)(\varphi) = \varphi\circ_M Ff = \mu_b\circ M(\varphi)\circ\eta_a\circ
f = \mu_b\circ\eta_{Mb}\circ\varphi\circ f = \varphi\circ f =
\hom_C(f, Gb)(\varphi)$ by naturality of $\eta$ and the left identity
law. For the other variable it is much easier, with $g: b\to_M c$,
$\hom_{C_M}(Fa, g)(\varphi) = g\circ_M\varphi = \mu_c\circ
M(g)\circ\varphi = \hom_C(a, Gg)(\varphi)$ for $\varphi : a\to M(b)$.

## Eilenberg-Moore algebras

An $M$-algebra (also called an Eilenberg-Moore algebra) is a pair $(a,
h)$ of an object $a\in C$ and an arrow $h: Ma\to a$, such that the
following diagrams commute:

$$
\begin{CD}
MMa @>{Mh}>> Ma \\
@V{\mu_a}VV @VhVV\\
Ma @>h>> a
\end{CD}$$

and

$$\begin{CD}
a @>{\eta_a}>> Ma\\
@| @VhVV\\
a @= a
\end{CD}$$

A morphism between two $M$-algebras, $(a, f: Ma\to a)$ and $(b, g:
Mb\to b)$ is a $C$-morphism $h: a\to b$ which is compatible with the two
algebras in the sense that the following diagram commutes:

$$\begin{CD}
Ma @>f>> a\\
@V{Mh}VV  @VhVV \\
Mb @>g>> b
\end{CD}$$

(One could also say that a diagram like this _is_ a morphism in
$C^M$.) The morphisms compose in an obvious way and we have the obvious identities, so $C^M$ is a category, the *Eilenberg-Moore category* of $M$.

### Some examples

In general, it is not clear for a given object $A\in C$ that an
$M$-algebra $MA\to A$ even exists. For a simple example, if $M$ is the
`Maybe` monad, then there does not exist an $M$-algebra $h:
M(\emptyset)\to\emptyset$, because $h(\mathsf{Nothing})\in\emptyset$
is a contradiction. It turns out that there is a 1:1 correspondence in
this case between $M$-algebras $h: MA\to A$ and *pointed sets* $(A,
a_0\in A)$ via

$$h(a) = \begin{cases}a\text{ if }a\in A\\a_0\text{ if
}a = \mathsf{Nothing}\end{cases}.$$

($h$ must send everything in $A$ to
itself due to the condition $h\circ\eta_A = \id_A$.)

If we take the list monad $L$, then there is a 1:1 correspondence
between $L$-algebras $h: LA\to A$ and monoids $(A,\diamond, e)$, by
$h([a_1,\ldots,a_n]) = a_1\diamond\cdots\diamond a_n$.

Interestingly, the list functor is the free functor to monoids, and
the maybe functor is the free functor to pointed sets. I'm sure this
isn't an accident.

## The Eilenberg-Moore adjunction

Let's again define a pair of functors, $F: C\to C^M$ and $G: C^M\to
C$. The functor $F$ must send an object $a\in C$ to an $M$-algebra,
preferably one that is somehow connected with $a$. But this is
difficult in general, as the previous section showed. Fortunately,
there is a canonical choice one more $M$ away: $\mu_a : MMa\to Ma$
automatically satisfies the conditions for an $M$-algebra, so we set
$F(a) = (Ma, \mu_a)$, the required conditions

$$\begin{CD}
Ma @>{\eta_{Ma}}>> MMa\\
@|                 @V{\mu_a}VV\\
Ma @=              Ma
\end{CD}$$

and

$$\begin{CD}
MMMa @>{M\mu_a}>> MMa\\
@V{\mu_{Ma}}VV    @V{\mu_a}VV\\
MMa @>{\mu_a}>> Ma
\end{CD}$$

are exactly the left identity and the associativity condition of the monad $M$.

A morphism $f:a\to b$ must then be sent to a morphism $F(f): (Ma,\mu_a)\to(Mb,\mu_b)$, we set $F(f) = M(f)$:

$$
f : a\to b\quad\leadsto\quad
\begin{CD}
MMa @>{\mu_a}>> Ma\\
@V{MMf}VV      @V{Mf}VV\\
MMb @>{\mu_b}>> Mb
\end{CD}$$

By naturality, this diagram always commutes.

The functor $G$ is simpler, an object $g: Ma\to a$ is sent to $a$, a
morphism $h: (a,f:Ma\to a)\to(b,g:Mb\to b)$ is sent to the arrow
$h:a\to b$. So $G$ is like a _forgetful_ functor, it simply forgets
structure.

We now construct a bijection

$$\Psi_{a,(b,g)}: \hom_{C^M}(Fa, (b,g))\xrightarrow{\cong}\hom_C(a,G(b,g))$$

Let $h: Fa=(Ma,\mu_a) \to (b,g)$ be a morphism in $C^M$. We ignore the compatibility condition and just focus on the part $h: Ma\to b$. By precomposing with $\eta_a$, we obtain a morphism $a\to b$, or $a\to G(b,g)$, so we can set $\Psi(h) = h\circ\eta_a$.

$$\Psi_{a, (b,g)}\left (
\begin{CD}
MMa @>{\mu_a}>> Ma\\
@V{Mh}VV        @V{h}VV\\
Mb @>{g}>>      b
\end{CD}
\right ) = \begin{CD} a @>{\eta_a}>> Ma @>{h}>> b \end{CD}$$

The inverse is not as easy, because we're given any old morphism $k: a\to b = G(b,g:Mb\to b)$ in $C$ and have to make up structure to form a commutative diagram. But we can do it:

$$\Psi_{a, (b,g)}^{-1}(k : a\to b) =
\begin{CD}
MMa @>{\mu_a}>> Ma\\
@V{MMk}VV       @V{Mk}VV\\
MMb %@>{\mu_b}>>
@. Mb\\
@V{Mg}VV        @V{g}VV\\
Mb @>{g}>>      b
\end{CD}$$

So we're just setting $\Psi^{-1}(k) = g\circ M(k)$. If we insert
$\mu_b : MMb\to Mb$ in the middle, we see that the upper square
commutes by naturality, the lower by the fact that $g$ is an
$M$-algebra.

Now I wrote $\Psi^{-1}$ without checking that this is actually the
inverse of $\Psi$. Let's quickly make up for that. Using the notation
of the previous paragraphs, $\Psi^{-1}(\Psi(h: Ma\to b)) =
\Psi^{-1}(h\circ\eta_a) = g\circ M(h\circ\eta_a) =
h\circ\mu_a\circ M(\eta_a) = h$, where we used the fact that $h$ is a
morphism of $M$-algebras and the right identity law for monads, and
$\Psi(\Psi^{-1}(k:a\to b)) = \Psi(g\circ M(k)) = g\circ M(k)\circ
\eta_a = g\circ \eta_b\circ k = k$ by naturality of $\eta$ and the
fact that $g$ is an $M$-algebra.

The last thing to check is naturality. In the first variable: Let $f :
c\to a$ be a morphism, then $\hom_{C^M}(Ff, (g,b))(h) = h\circ Mf$,
which is sent to $h\circ Mf\circ\eta_c = h\circ\eta_a\circ f$ due to
naturality, which is just $\hom_C(f, G(g,b))(\Psi(h))$. In the second
variable: Let $f : (b,g)\to(c,h)$ be a morphism in $C^M$. Then
obviously $\Psi(\hom_{C^M}(Fa, f)(h)) = \eta_a\circ h\circ f =
\hom_C(a, Gf)(\Psi(h))$.

# The category of adjunctions that form a given monad

There can be many adjunctions that form a given monad $M$. Let's call
them $M$-adjunctions. To relate them, the elementary idea of category
theory tells us: Look for the morphisms!

Let us denote an $M$-adjunction consisting of $F:C\to D$ and $G: D\to
C$ by the triple $(D, F, G)$. $C$ is implicit, since $M$ is an
endofunctor of $C$. A morphism of $M$-adjunctions $(D_1, F_1, G_1)\to
(D_2, F_2, G_2)$ is a functor $K: D_1\to D_2$ such that the following
diagram commutes:

$$\begin{CD}
C @>{F_1}>> D_1 @>{G_1}>> C\\
@|          @V{K}VV       @|\\
C @>{F_2}>> D_2 @>{G_2}>> C
\end{CD}$$

that is, we require $F_2=K\circ F_1$ and $G_1 = G_2\circ K$. These morphisms compose in an obvious way, so we obtain the category of $M$-adjunctions, $\mathcal A_M$.

The rest of the article will be dedicated to showing the roles of the
Kleisli and the Eilenberg-Moore adjunction in this category, and to
illustrate the findings on our initial `State` example.

### Theorem:

Let $(M,\eta,\mu)$ be a monad on a category $C$, and let $\mathcal
A_M$ be the category of $M$-adjunctions.

1) The Kleisli adjunction $(C_M, F_M, G_M)$ is an initial object in
$\mathcal A_M$.

2) The Eilenberg-Moore adjunction $(C^M, F^M, G^M)$ is a terminal
object in $\mathcal A_M$.

#### Proof:

Let $(D, F, G)$ be an $M$-adjunction, given by
$\Phi:\hom_C(FX,Y)\cong\hom_D(X,GY)$.

1) We define a functor $K:C_M\to D$
such that $K\circ F_M = F$: Since $F_M$ acts as the identity on
objects, we have no choice but to set $K(a) = F(a)$. On morphisms $f:
a\to M(b)$, we set $K(f) = \varepsilon_{Fb}\circ F(f)$.

First, we show the functor laws. The identity corresponding to an
object $a$ in the Kleisli category is $\eta_a : a\to_M a$, and
$K(\eta_a) = \varepsilon_{Fa}\circ F(\eta_a) = \id_{Fa}$ by the
triangle equations, so $K$ preserves identities. If $f:a\to M(b)$ and
$g: b\to M(c)$ are Kleisli arrows,

$$\begin{align*}
K(g\circ_M f) &= \varepsilon_{Fc}\circ F(\mu_c\circ M(g)\circ f)\\
&= \underline{\varepsilon_{Fc}\circ FG\varepsilon_{Fc}}\circ FGFg \circ Ff\\
&= \varepsilon_{Fc}\circ \underline{\varepsilon_{FGFc}\circ FGFg} \circ Ff\\
&= \varepsilon_{Fc}\circ Fg\circ \varepsilon_{Fb}\circ Ff\\
&= K(g) \circ K(f),
\end{align*}$$

by the diagram associated with $\varepsilon\bullet\varepsilon$ and
naturality.

Now we've already seen $K(F_M(a)) = F(a)$ for objects $a$, and for
$f:a\to b$, we have $K(F_M(f)) = K(\eta_a\circ f) =
\varepsilon_{Fb}\circ F(\eta_a)\circ F(f) = F(f)$ by the triangle
equality.

Also, $G(K(a)) = G(F(a)) = M(a) = G_M(a)$, and if $f: a\to_M b$ is a
morphism in $C_M$, $G(K(f)) = G(\varepsilon_{Fb}\circ F(f)) =
G(\varepsilon_{Fb})\circ M(f) = \mu_b\circ M(f) = G_M(f)$.

It remains to show that the action of $K$ on morphisms of $C_M$ is
uniquely determined. Let $L$ be another functor $C_M\to D$ such that
$G\circ L = G_M$ and which satisfies $L(a) = F(a)$ on objects. We're
going to use the interplay between $\Phi$, $\eta$ and $\varepsilon$
now. For a $C_M$-morphism $f: a\to_M b$, we have $G(L(f)) = G(K(f))$,
hence $G(L(f))\circ\eta_a = G(K(f))\circ\eta_a$. We can rewrite both
sides in terms of $\Phi$: $\Phi_{a,Fb}(L(f)) = \Phi_{a,Fb}(K(f))$,
from which follows $L(f) = K(f)$, because $\Phi_{a,Fb}$ is a
bijection. We conclude that $L=K$.

2) We define a functor $T: D\to C^M$ such that $T\circ F = F^M$ and
$G^M\circ T = G$. Since $T(FX) = F^M(X) = (MX, \mu_X) = (GFX,
G(\varepsilon_{FX}))$, an obvious choice is $T(Y) = (GY,
G(\varepsilon_Y))$. This also satisfies $G^M(TY) = GY$.

For a morphism $f:X\to Y$ in $D$, $T(f)$ is a morphism in the
Eilenberg-Moore category between the free $M$-algebras $T(X)$ and
$T(Y)$, but as $G^M$ is a forgetful functor, the condition $G^M(Tf) =
G(f)$ forces $T(f) = G(f)$.

$$\begin{CD}
MG(X)   @>{G(\varepsilon_X)}>>   G(X)\\
@V{MG(f)}VV                    @V{G(f)}VV\\
MG(Y)   @>{G(\varepsilon_Y)}>>   G(Y)
\end{CD}
\quad\leadsto\quad
\begin{CD}
G(X)\\ @V{G(f)}VV \\ G(Y)
\end{CD}$$

The remainder of the proof is dedicated to showing that $T$ is
uniquely determined. It is clear that we had no choice in the
definition of $T(Y)$ for objects $Y$ in the image of $F$, neither did
we have a choice in the definition of $T(f)$. It is not yet clear that
$T(Y)$ must be $(GY, G(\varepsilon_Y))$ in general. This has to do
with the seemingly arbitrary choice of $\mu_X$ as the "free
$M$-algebra" $F^M(X)$. Just because we can't think of anything else
right away doesn't mean it's unique.

We proceed in three steps. First, the following diagram is commutative
for all $X\in C$, $Y\in D$:

$$\begin{CD}
\hom_D(FX, Y) @>{\Phi_{XY}}>> \hom_C(X, GY)\\
@V{T_{FX,Y}}VV                       @|\\
\hom_{C^M}(F^MX, TY)  @>{\Phi^M_{X,TY}}>> \hom_C(X, GY)
\end{CD}$$

Here, $T_{FX,Y}$ denotes the action of $T$ on morphisms,
$\hom_D(FX,Y)\to\hom_{C^M}(TFX, TY),\,f\mapsto T(f)$. Keep in mind
that $TFX = F^MX$ and $G^MTY = GY$.

To see that this is true, realize that $\Phi_{XY}(f) =
G(f)\circ\eta_X$ and $\Phi^M_{X,TY}(T(f)) = G^M(T(f))\circ\eta_X =
G(f)\circ\eta_X$, too.

Second, recall that the counit $\varepsilon$ arises as the image of
the identity under the inverse adjunction. Thus
$\Phi^M_{GY,TY}(T(\varepsilon_Y)) = \Phi_{GY,Y}(\varepsilon_Y) =
\id_{GY} = \id_{G^M(TY)}$, therefore $T(\varepsilon_Y) =
(\Phi^M_{GY,TY})^{-1}(\id_{G^M(TY)}) = \varepsilon^M_{TY}$, for all $Y\in D$.

Third, $\varepsilon^M_{(A,h)} = h$ in general, so the structure
morphism of $T(Y)$ is $\varepsilon^M_{T(Y)} = T(\varepsilon_Y) =
G(\varepsilon_Y)$, for all $Y\in D$.

This concludes the proof.

# Example: Decomposing the `State` monad

# Notes

* In fact, the currying adjunction is the only adjunction inside
  $\cat{Set}$ and the `State` monad is the only monad that is formed in
  this way (up to isomorphism.) We're going to look at this issue in
  another article.

TODO Unify notation. Objects $a$ vs. $X$? Adjunctions $\Phi^M$ instead
of $\Psi$.

TODO Think of a better way to denote an object of $\mathcal A_M$.