// Local fork of unequivocal-ams:0.1.2 with an added `running-head` parameter.
// When `running-head` is provided it is used in odd-page headers instead of
// the full title, preventing long titles from wrapping across two lines.

#let script-size   = 7.97224pt
#let footnote-size = 8.50012pt
#let small-size    = 9.24994pt
#let normal-size   = 10.00002pt
#let large-size    = 11.74988pt

#let ams-article(
  title: [Paper title],
  // Optional short title for odd-page running headers.
  // Defaults to `title` when omitted.
  running-head: none,
  authors: (),
  abstract: none,
  paper-size: "us-letter",
  bibliography: none,
  body,
) = {
  let names = authors.map(author => author.name)
  let author-string = if authors.len() == 2 {
    names.join(" and ")
  } else {
    names.join(", ", last: ", and ")
  }

  let odd-head = if running-head != none { running-head } else { title }

  set document(title: title, author: names)
  set text(size: normal-size, font: "New Computer Modern")

  set page(
    paper: paper-size,
    margin: if paper-size != "a4" {
      (
        top: (116pt / 279mm) * 100%,
        left: (126pt / 216mm) * 100%,
        right: (128pt / 216mm) * 100%,
        bottom: (94pt / 279mm) * 100%,
      )
    } else {
      (top: 117pt, left: 118pt, right: 119pt, bottom: 96pt)
    },

    header-ascent: 14pt,
    header: context {
      let i = counter(page).get().first()
      if i == 1 { return }
      set text(size: script-size)
      grid(
        columns: (6em, 1fr, 6em),
        align: (start, center, end),
        if calc.even(i) [#i],
        upper(if calc.odd(i) { odd-head } else { author-string }),
        if calc.odd(i) { [#i] }
      )
    },

    footer-descent: 12pt,
    footer: context {
      let i = counter(page).get().first()
      if i == 1 {
        align(center, text(size: script-size, [#i]))
      }
    }
  )

  set heading(numbering: "1.")
  show heading: it => {
    let number = if it.numbering != none {
      counter(heading).display(it.numbering)
      h(7pt, weak: true)
    }

    set text(size: normal-size, weight: 400)
    set par(first-line-indent: 0em)
    if it.level == 1 {
      // Prevent a section title from being orphaned at the bottom of a page.
      block(breakable: false)[
        #set align(center)
        #set text(size: normal-size)
        #smallcaps[
          #v(15pt, weak: true)
          #number
          #it.body
          #v(normal-size, weak: true)
        ]
      ]
      counter(figure.where(kind: "theorem")).update(0)
    } else {
      v(11pt, weak: true)
      number
      let styled = if it.level == 2 { strong } else { emph }
      styled(it.body + [. ])
      h(7pt, weak: true)
    }
  }

  set list(indent: 24pt, body-indent: 5pt)
  set enum(indent: 24pt, body-indent: 5pt)
  show link: set text(font: "New Computer Modern Mono")

  show math.equation: set block(below: 8pt, above: 9pt)
  show math.equation: set text(weight: 400)

  set std.bibliography(style: "springer-mathphys", title: [References])

  set figure(gap: 17pt)
  show figure: set block(above: 12.5pt, below: 15pt)
  show figure: it => {
    show figure.caption: caption => {
      smallcaps(caption.supplement)
      if caption.numbering != none {
        [ ]
        numbering(caption.numbering, ..caption.counter.at(it.location()))
      }
      [. ]
      caption.body
    }
    show selector.or(table, image): pad.with(x: 23pt)
    it
  }

  show figure.where(kind: "theorem"): set align(start)
  show figure.where(kind: "theorem"): it => block(spacing: 11.5pt, {
    strong({
      it.supplement
      if it.numbering != none {
        [ ]
        it.counter.display(it.numbering)
      }
      [.]
    })
    [ ]
    emph(it.body)
  })

  // Title block
  v(35pt, weak: true)
  align(center, upper({
    text(size: large-size, weight: 700, title)
    v(25pt, weak: true)
    text(size: footnote-size, author-string)
  }))

  set par(spacing: 0.58em, first-line-indent: 1.2em, justify: true, leading: 0.58em)

  if abstract != none {
    v(20pt, weak: true)
    set text(script-size)
    show: pad.with(x: 35pt)
    smallcaps[Abstract. ]
    abstract
  }

  v(29pt, weak: true)
  body

  if bibliography != none {
    show std.bibliography: set text(footnote-size)
    show std.bibliography: set block(above: 11pt)
    show std.bibliography: pad.with(x: 0.5pt)
    bibliography
  }

  v(12pt, weak: true)
  show: pad.with(x: 11.5pt)
  set par(first-line-indent: 0pt)
  set text(script-size)

  for author in authors {
    let keys = ("department", "organization", "location")
    let dept-str = keys
      .filter(key => key in author)
      .map(key => author.at(key))
      .join(", ")
    smallcaps(dept-str)
    linebreak()
    if "email" in author [
      _Email address:_ #link("mailto:" + author.email) \
    ]
    if "url" in author [
      _URL:_ #link(author.url)
    ]
    v(12pt, weak: true)
  }
}

#let theorem(body, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Theorem],
  numbering: if numbered { n => counter(heading).display() + [#n] }
)

#let proof(body) = block(spacing: 11.5pt, {
  emph[Proof.]
  [ ]
  body
  h(1fr)
  sym.wj
  sym.space.nobreak
  $square.stroked$
})
